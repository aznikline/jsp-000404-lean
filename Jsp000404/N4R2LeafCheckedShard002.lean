import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard002
open N4R2RowDataReplay

-- Original cycle 0093b840213dcc303e0302caf2a98fcd51973a5c210bf29422cba2556f5f4b22; original global index 50.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 02b6628f04c7da6e7c7b864ecdc4900b02292e07f8e6561aeddd59d2885c3920; original global index 212.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 03ebbf996e97d765a690b240d1c3b23246539a91837f2d1125065be63dc8e630; original global index 310.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 050a1c65b97eb20a5689325818c3ff49fae2228c95b3ee9d3cb415be3d616e61; original global index 406.
def localCycle00003 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 07c1dfd833c9d222abe1e77dc9cb1223cf45bcd80b8e5ec84f107b08c1a588ce; original global index 632.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 2, .gapLower 6 4, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 09283ccdacceccc9d41b688cfd5600e192eec8dab2e25ec780033eefd072bfb6; original global index 731.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 0ae3c1e14b119840dde75e1959efd4a484f4848afb772a3c15247baddb6da57c; original global index 867.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 3 6]

-- Original cycle 0b28a83c3b72e71c5cdbe76164a0f4f1bfc8542d6f7843a975b1deb52d7e8cfc; original global index 893.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle 0b68e6dfc71ff4413bff41304ba39527d25e597912e5cbf8dcc2e86cbf422e48; original global index 915.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 0ce2d72e4aa7d88a12947e458bd1e0b89ae3265902ebbaa383f2caadf32c01d3; original global index 1016.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 0db00fe9156fbfbfb9ab61cb5f5e1acf891b78b9de4cbfc89eb356f932b75132; original global index 1082.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 11 2, .gapLower 6 0]

-- Original cycle 0e4b04379d326e1ebed1ed03804fb06a2c71cfa19a8a89cd25822d596bf5eba7; original global index 1124.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .gapLower 6 3, .triangle 11 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0e540e476fb20faace19a23dff1d41b41f6abd66151d80c5fc67a590f3900a9b; original global index 1130.
def localCycle00012 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0f2f39c94cf3ebc2bd469c7db6ee7889883a2dc55f28138b92e968ef2eab8147; original global index 1212.
def localCycle00013 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 111a2c01b9baeaa9cf7436c5e3934a4ca297bd3aabfa0ae56a7f5f86f47162db; original global index 1365.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1476fe5050c5da13b18d2121430013a682e92e7e9211304fd6c7e98875e5f9c6; original global index 1619.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 15cbc4a8045ca6fcf190876efd27485dadd8042b4034f51c97178c8ba9c095b4; original global index 1731.
def localCycle00016 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 17a0e0ad45fa34a6a54dcbb4c6495220a4c54e23a55adcfc6c7f984df2cb43bd; original global index 1847.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 17b3a28ff982f05952fe9ff8bd9d65f3cde6248743bc9080c5f9c9cc7a1ac249; original global index 1853.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .gapLower 6 1, .triangle 11 1, .gapLower 3 0]

-- Original cycle 1924ae3905c41e8ec23ee72a174782dcb7ae76bb99b43ffe661da808fba2606c; original global index 1961.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 1b28dff94edba3354fd308506f9f0d275cf882869fb3214b2db16173148e02e4; original global index 2103.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 1ce35ca6175e49577be5ecb4d53bebd6a733c51f71cb3b13d2f1c5c55f6d295b; original global index 2225.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 1ce58b3d8a89a61adf0191db6c78a4a90800bb1e30fbdd819edab05791291ed4; original global index 2228.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1e986e59de2eee6d7d4f91dc97054d4fc69200b3149733e3f62d1231c9a9ac12; original global index 2348.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 1fa983a250a67db27c8f95644a6e35580429b7a18945ef5936311c4142b4be11; original global index 2436.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 20e09b5c66cdc1cbcd7daab5ffb50816ac317bb34982ab7a36c585be9577c848; original global index 2521.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 2292e30deee13aaebb42176b0718d60f16b95431b6791738ec51a2133e418a4b; original global index 2645.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 254a535fc594a289e54d0e65edc239cd770cccae96d8a8d94a4ed6454d390776; original global index 2867.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 25ef1ab104fe4deb36254dba6ef93c66bc29fad3613b85e56760966c1962a6d1; original global index 2908.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .triangle 21 1, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 28aae35961410d7eca267f9c683b2df3c6063bf5cfc56fb26c32c9319cfed45e; original global index 3113.
def localCycle00029 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 298ec2dad45665bd56e18f3386a751d8f782e941290493b50c509887f1148346; original global index 3170.
def localCycle00030 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0]

-- Original cycle 29b96857ceed9669d9fc8e7d632db98bbff84fd0d2c0a19707614ac43a1e4377; original global index 3185.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 2a0418d88f1ecd015670210a7b98326a08f73f22d5425f68ca2ba726ec243c68; original global index 3204.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 2b04ebf426b43cd9dd1d1f12e067fa7f5e5d815982c48dbd17b596bc63f6b250; original global index 3284.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 2ea882992159df4407d6892f81e50feaf7e0157d2a688bec27c729201b95e956; original global index 3563.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 2eaad7fdbcafc473de9a39ad864d6365dd563a742fd11ff30e74c8cdca3b06a9; original global index 3567.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 30c74e5bd7c02d8fe3f832692c5997689fcdebbc515b535d6a401260d1e9fe20; original global index 3721.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 31b740280481f3e7ce191ee6c7a28450d093994d2e65756236821285ae819014; original global index 3797.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 1, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 32503f1a94d936560b03478d9afae744a387939488786b6c7f919b51539a6c1e; original global index 3843.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 33d49523e6a4710ded22088319f15a549d467f0f003b6fd824d74af9d7f83f89; original global index 3972.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 15 0]

-- Original cycle 3497131ef86db7195d5495782cc549f59f6cb0be0eadb4b712472c8da191008d; original global index 4026.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 354284a1a2b7ea7b730f66523638efae44e76382af3a11127ca91612fb955cf9; original global index 4075.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .triangle 34 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 35fc0a7e6f595d5d2b12bf5e58f6ff09485571d1752c24cd5dd1fda15497c63f; original global index 4144.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 36562905db2bfb79dd8d3d87b027b474c14bfbcb8e9bfba1aa6e13c419d1757a; original global index 4167.
def localCycle00043 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 0]

-- Original cycle 3739f79cd3e0e42b98829476dea3b96ed23da25db7e82d767e88f3eeba981db1; original global index 4241.
def localCycle00044 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 2, .gapUpper 3 4]

-- Original cycle 38a34dafc1e47738eb6ebf048a237c350f7364083da79e19de66e4384311d224; original global index 4357.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .gapLower 3 0]

-- Original cycle 399b6b9e662dffd820722485d41ce86907b8150ef0ea43da3ec4da79b5e84b7c; original global index 4440.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 3a07d5937c228a770b60958b238de0d8c779488cedbec72d8249b360db280515; original global index 4477.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 3d4fc1f4b17b26c39001c917cc03adbb07f035ece3cfd83387dfb7a52f7fc45d; original global index 4749.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 3d9201047a9601a34bb78a4f33051731afe0b505f0730b820c1acc859f4d9d2c; original global index 4766.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 30 1]

-- Original cycle 4007896e30b41ad49a517bb29a7fa85a377aea067678275aded96f686d5f9d62; original global index 4938.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 40c8ab40953d39f33342a138dd71e64caec396237762bd61b881447b9aecb3c7; original global index 5004.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .triangle 24 1, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 427cc6998d3d4604ea76e26f862692e55e78dd76f88212d81be8a61ccca67488; original global index 5124.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 454266f25e90e8da6e5ef0ddf003a2cf02299f6a09439cccf7aba4f9d9ae5a96; original global index 5357.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 46358cd9d03e22fcea1da8082af2c91f972ce1ee08a10d64678c496a6bf459ae; original global index 5434.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 4724eb4e3e52e0c0cc43ba37bb715ef8551425795c4637fec6b8d1f3abc76568; original global index 5518.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 485e1c97b27f10cae00a60380e6f5d8d3604a0005fcf7989700c86f8e375c609; original global index 5602.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 486f0b749b2b5363a07f4416413d7147c1da06be7269dce19b6334a806cc70e4; original global index 5608.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 24 1, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4ad0ef313437cf3a87469943b8c8cd9a0893e4121f3c23c2b53523a23ebebc3a; original global index 5807.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 4ad25ca6f6f7b88a092dbbc586c75f6e8cdb119fecb140bee85a6f6d5f8b78e8; original global index 5808.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 26 1, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 4b7b03a10cd387167cff09be66dd19fa68702059f265d754026833b2bf34c2c2; original global index 5850.
def localCycle00060 : Cycle where
  length := 19
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 6, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 2, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 2, .gapLower 6 0, .gapLower 6 6, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4cac2db3606e3dd2f8454d3d972b273a31f2565151a3960e349170d9501af686; original global index 5949.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4cb997f4a49dbb3bb6f33451d1c1380d89e038f36bb68c6ba374e1e71fcfe228; original global index 5955.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4d39e0884a851d57c3482e5bfd9bb45bcc58410da41c14d1c6b8a3bbdf18b466; original global index 5997.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4da38d176c12518a112f5e44f3bb27f6ac0643aab7a98f3ddb5fc6e8b0411628; original global index 6031.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4ef1748feddc221cd2e9f87dd26771735c166ef5728edd892b413c60d1d15932; original global index 6134.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 51260c85946f28b9d88479db4c5ac577822a9b10b0024b8e908eb65b567d8fae; original global index 6305.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 51a8e986661b90e962b1187d17c382fe04ab0def74e7e88711a36f7e05af7b94; original global index 6354.
def localCycle00067 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 51ad3ad116f5d032ea8cec09fc4775f69fa5dd5e29389d1c077584a5a27847a6; original global index 6357.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 52b8c2834448990b8b7f9aa1e139e3c36768b620bf2b46735d05ea675c87a6b0; original global index 6433.
def localCycle00069 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle 52cbc054bb789cb9d19c3b64c0d268e966d454a442f1001445156a7d9a062361; original global index 6439.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 18 2, .triangle 21 1, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 52d710e2e12463c34e81d8d0c72125d9de93499367d2e4dd42b68e337b245f75; original global index 6450.
def localCycle00071 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5378161960b7118c45e75bc684c41d1703aeb4a84e699ecea74daf440f51ffa8; original global index 6487.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 548fc30a411291122aeec95563de62268b24959c1570d8c81dcece1be8be747f; original global index 6553.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5ec85f8589e3e6420fe6c87593de7cf3559b4eaf0061f72b5e443abb6840f7b8; original global index 7379.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .corridorLower 3 4]

-- Original cycle 61733db81fe8a2780bc78b178f804049b57b089a669eb93525ae73634740ebcd; original global index 7599.
def localCycle00075 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Original cycle 620312acf1703c1197cc9619127a8c0e4c02bed2f2ece7008cf198d0d41e506c; original global index 7652.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 66ff1897ddfeae1761ee5b7cf5f420775541a4fb44c7c987bd122aa05743c888; original global index 8001.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 681d9618752471661c432b9e0a06e55744f63b8a4e30c092252355b83d5ed165; original global index 8091.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .gapLower 6 4, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 69580338fb722790b592a216bbd60b61318057f71594034966f9304418f444b9; original global index 8196.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle 6a3bff9d3c348328d43da90f90e73cc3905ac41a2831057156143c1fdca7fbea; original global index 8271.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 6a57f3fdfa27af23a704dcf7b63dc1d9af1693e49fc705caaf7859f6a6a984e3; original global index 8280.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 6bccc2fff60c1ea4e466cccdeb2f56b713682b09137b4a7db9eab3dcd66e6376; original global index 8396.
def localCycle00082 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 21 1, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6bda16f572d615be69377141095a25035bce0960a59cf417b6c41ccde2df5f32; original global index 8401.
def localCycle00083 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -3, 0, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6c9f7bc94b2ed46443034884d47003a3dfe0d290ca8ce4809141341f1956c862; original global index 8450.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 6dc77dae9591bfe57e2b63b959ba8372962f0c5ac9fba20427b292a5a6809d31; original global index 8531.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 4, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 6e2ed1693b7dc6d83404b5e8917c9552df1ec5e7fbf8dd8cd3d306d6cd8f8829; original global index 8553.
def localCycle00086 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6e47adcab3f2580063a2cff0600a9e3ed96ae598ef183c4f39fe861b39718a70; original global index 8560.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 6feffb507363e3f7f4cfe06bcd5681fde07420539e2cb00ec5b6773be59bf2ba; original global index 8679.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 19 0]

-- Original cycle 73847055569961743fca793c3611c82b683b7b38e6097fe23e21ae18162db432; original global index 8955.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .triangle 24 1, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 7392e48ac379b717e22a0a4c14245ffc9a0da2fb0be67cb23ddb88ca0a48293f; original global index 8961.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 73d7640b3be0f7cf8dec3d3d1d7f654551e41804ed053dfd5030240ece5dc9da; original global index 8983.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 74023cc5745eea18bcc4ef1338b1522d7f9980be75554e2280a56a89dc9846c9; original global index 8999.
def localCycle00092 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 76a9038bf60461c7ae5d7d927109b3743256acef037b92421b04ecf2ef142bff; original global index 9185.
def localCycle00093 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 33 1]

-- Original cycle 76c20cacb30145dc8c9658833df341d0e67c04c82e23392e31664853025e0688; original global index 9190.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 76e4136af6a8b3da1b74a6e952566b7245af0d64a809ec762034462225f8139e; original global index 9202.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 4, .triangle 15 1, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 78766160a0e40d1eb2ceae1353382c8a9525434cf991bec50c6d559ef7761491; original global index 9318.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 78cb25843bd7e4d9d41b9739a7a3f39c3418714a574acceb1d45bfeeac05a14c; original global index 9347.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 78dd18e33d0b1e652a39006ca95ac29faf2f0a04fc4ec112409f167c9a41a633; original global index 9351.
def localCycle00098 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7b7fb8ff4088cba9130a80a0c92e5cc259eaba31d0a79f5b0835b1c61291dff1; original global index 9558.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7c1748d6abdb68a414aff5972447b77597509f8d3fd5125766d762af83effc8b; original global index 9600.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 7c6e1a224062d865f5cf17b02b6c5d447345b41d506279c5501ad73bb7ef08c7; original global index 9629.
def localCycle00101 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 1]

-- Original cycle 7e62e88360371b77a22424e56fa368d0c979c5b6dbd2b458f0fd9e8970735b0c; original global index 9817.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .gapLower 6 1, .triangle 11 1, .gapLower 3 0]

-- Original cycle 7e700f18a15088f4c77c5fad4e2831a5c99df6e4a01184ead22b78c6c7aef532; original global index 9821.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 7f5254db735348cbfe6093fc849c9e057a5709ff4331d98a3117fe2a7d971fba; original global index 9873.
def localCycle00104 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 18 0]

-- Original cycle 7f930275935b33845287758aa580ccb1f2cd9717c3712d83aad3b28d37db080a; original global index 9895.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 82126c5cb9c27aac91d9af65a58226a039556dbb65df050b00b55ae78c26df30; original global index 10099.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 83a93ed9bbff427e06762b5c6a93f9d027665b593eeda1eb678bec59006d3fc8; original global index 10219.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 83b99d5aaef2dd1af2d01b784d0b8efbbf004cf968ccf7959c3d3c4cd4deaecb; original global index 10223.
def localCycle00108 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 3 6, .distance 1 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 21 2, .gapLower 6 2, .gapUpper 3 4]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 886d04b1acc0b8039cbf8f874b3cb295c3a916cae978c35688d369e5d36986c5; original global index 10570.
def localCycle00110 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0]

-- Original cycle 892438758687eed8b3485b6f2c098406c2b52f0ec02a1055fe08546e8b6e1a04; original global index 10613.
def localCycle00111 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 18 1]

-- Original cycle 89425802499d96782d62ceb50f36ad9ef80379c0d6aca178f4a953bab5ccb6e9; original global index 10622.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 8a89a97a51beb062890cb94daa205184d1eb00dc59a0a10ec636bba31961b5c6; original global index 10731.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 8a9febebd42526c60492d91a15deebc69c289bdb54b940513ae61f47d5563b64; original global index 10738.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 8ac53bc094caf1f386d1fa2de2c890ce8efc3f1eecdc7a0060632be5dd186139; original global index 10751.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, 0, -1, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .triangle 21 1, .triangle 32 1, .gapLower 6 1, .triangle 11 1, .gapLower 3 0]

-- Original cycle 8c1ce425dcfd1e0ca81be184a7fa9bc75f43834aabaf5de775323511544f4caa; original global index 10847.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 8d38f7e2498f521e790a210601c8097f6b5801cebaaf72ef9703d8ec79df7a0d; original global index 10918.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8d4b1314d90efba8904eaae41b14e89c24324aaf6e37055a6c111f0aee0a65d0; original global index 10924.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .gapLower 6 2, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 8e17251990210b35d356a85958c6d92052bc484744ae532432be50ce64ce5159; original global index 11004.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false] }
  origin := ![.triangle 16 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 3]

-- Original cycle 9069e5db89dc8ceaeee0b47e28e3a7a4d22db7478e24ba5cef95d8af839e9834; original global index 11180.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 90c8fe291111c82e795206e8fdf3fef28bf600b7cbdd2a0e950ce3d502e250cb; original global index 11214.
def localCycle00121 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9270f686fac76d9f2d933b022f5ea81d6ec42e47c091f3f7749af3ddcdf1bdc6; original global index 11341.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .triangle 13 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 92ce83c9da10931539fab072f921e861b4de0fc9c4b2e30d22e39d4895c380de; original global index 11377.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 931a391d82b8c82a02b50f7e12d7b7bacf7bcc48d00beb69e32102e36770e248; original global index 11405.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Original cycle 935eaeb414d65cfd77a988f439947ba6367e6a4768a9e25b7e26726211712e47; original global index 11429.
def localCycle00125 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 24 1]

-- Original cycle 93b5abf3c3a2d3a6379df32be3e314aa59f4d05c8166cfb8099c9315c078f154; original global index 11458.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 957c03792a88374e0ccbd026d9834d3d93c0aa29dcbaab528aa77896d5b69976; original global index 11618.
def localCycle00127 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 9745a276b97e8f43ec274c286a9f9cd8530a28977b4a88d614fb77e167eb77a7; original global index 11755.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .gapLower 6 4, .triangle 21 1, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 9a007a456920fea3f2c51eac017706fdbf92f3ffe904aafa1eff5f88f9735008; original global index 11957.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .triangle 11 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9a04270df0e4f62671fd3ad8889e9d8716616a7b7a2c3425ad80750e0fc1c1c0; original global index 11959.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 9c372e8a85c9b74def3e165b0ce18d90668678b2f568362218f2e5117aa77335; original global index 12154.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle 9d04ad2b37561ca294af4fc302dbdc77465d915d7f46306d5f277d113e0a56d0; original global index 12213.
def localCycle00132 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle a143b595e06980b402e55303830f5b41753078fa9bd03bfaed83c1404a2d72de; original global index 12540.
def localCycle00133 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 0, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a2d1020ff02e74fae1fde9cc95b58ff4c0a42fc6596e591a15066c50ad735cdf; original global index 12663.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a4b57fcd40cb1beb702235ff56ea428c3df804e06ba0ab4eb46f2b635bc798aa; original global index 12800.
def localCycle00135 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a74d2ff1b8338da6f90227ab4958a2d4807ce559f2cfb2da6166caf10af63f37; original global index 13011.
def localCycle00136 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a7cb37a65579ca5cb4c26e640e375c61a04780ad150f080f6aa2b30bc292568d; original global index 13055.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a7e8f84a03e16f7579463fbfe6f766c8abf41e84f00a4ec2ae87f6be7f3ba355; original global index 13071.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle a83be8d5695825a6a4ec2e4a18b10975e0a17067b3c782b742920ef91f3e64af; original global index 13100.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle a9f9b2f2c91dae7b160440075fc0613d8d723528f26a14a473520a1a0a6a535e; original global index 13231.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 6, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 2, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle aa8e1ab38e50b93fd8a7257890539a81e589eba6d4bde628e7aeed9317e47181; original global index 13284.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ab3582250043336750c327a125b744806d6abeb0585f7025960b8fdd2ef21b44; original global index 13338.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle ac84965af6eb23fbb573cf8b53f4b99e426d5a52703213198722a85e75ad65fa; original global index 13446.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle ad986be5a967c260991834838c9bb1dddd92d51dfe9582a0570515316a6ddb4b; original global index 13549.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .gapLower 6 2, .gapLower 6 1, .triangle 11 1, .gapLower 3 0]

-- Original cycle ae75addfb23f94cb8548440322fdc0077bb803b6861e3fc88dbf1dbfd674b2ca; original global index 13618.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle b0d07812399bcdc4b8b054ae20bc6165ceaf520fa40eeb1ad7ffdeb55ed54e25; original global index 13808.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle b1631a50e2542a4b8ca78b1b4ef8a2ff79dc380b65390dca20a49b09dfcba0b7; original global index 13859.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle b3a754fc88ff34509630ece9e5913c2a48afa6a9ffb1f74c736448c1b01b0604; original global index 14032.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .triangle 11 2, .gapLower 6 0]

-- Original cycle b425bcd88af549f20f34d5e5dbd70683e48c2cc8c3091b3ad812d16c3aafb6e8; original global index 14068.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle b94fb0559ebd2dd2857f868638b86bd1bf48d906321ab055725a6c34ef98c9eb; original global index 14459.
def localCycle00150 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle b95ecb5e3d9f7c923e8f0a988d664dacfc79fdc5e110f0e54252acd2c03bce79; original global index 14464.
def localCycle00151 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 30 1]

-- Original cycle ba367ed03a5d3b3bb54741f010fa8a00e4ce6f7576f0deda6aa5be2989509adb; original global index 14538.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle bad6d792bbfd431ba1071e8a76dac2cf34565f8b164aac358f55b4179bdfbe84; original global index 14594.
def localCycle00153 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 2 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 5 5, .gapLower 6 5, .triangle 29 0]

-- Original cycle bce286f1392effab3cd1493fc0d1b54a53966871684a2c77d8497f8ebd5f228f; original global index 14735.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bda659af50738dd02e9c9d1aba13fca736a95df92a8627a6a5ddac35cdd5af42; original global index 14794.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bf1dee944e5855ecedf57c82cfab5e7e40a42b8a67b175f650b75d389ce15a32; original global index 14911.
def localCycle00156 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -3, 0, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bf5bae3ce3b3ea74e47afbffe35960d51396c5e50a604ab2e0c4c2680152a187; original global index 14933.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c07c95b0b128f60a92243fd7aff872d1ab14a6e4a5a0a5a6845aa9eeaf6f0ed4; original global index 15026.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c149e9c9987dd872cd8bb26d7d775567f41c6f566f16ccef2b549e5544e4bfed; original global index 15092.
def localCycle00159 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c17c60d2147875c4c778bc4cd9a16d277d271f5b3390d2fd83fecb2b35331884; original global index 15111.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle c27dfa0024fff03b07b3c242b5471ebff08ac4c0ad5fb2b4d4590f2cebfc8bfb; original global index 15183.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 17 2, .triangle 24 0, .triangle 34 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c4a2cab4d86d5acf50c3caf8918c8227abae654a89c6e1e8003076f74c6076a2; original global index 15333.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle c575125de064985c7a95531c8004b790dd47045cd6d67f0db1bd306644b06674; original global index 15405.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c5db05817cf0de20c99fafe73630a5355573c66d9e004a65099fc479d57a66ef; original global index 15427.
def localCycle00164 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c7850626a18a11aa5e7640740cb7eb8542498553c3ba3661318401c4c57ad5f7; original global index 15571.
def localCycle00165 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c7d64923c1c86293d049d022c69096271ff7af4c9848252b5a1278a1142de32e; original global index 15604.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle c87e313d19505b6fe7d36083a6bfaaa113a8efd9693a5fa1aa551bb3f9455aaf; original global index 15658.
def localCycle00167 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle c998b3e6424f71ad41faf31dd4ccd509cb490f912279083d9ce4f47eed9dbe6c; original global index 15762.
def localCycle00168 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle ca012fc96290984c31eeca5546a9ff27c291496ff099891bb21e8b7d3ceeaac1; original global index 15788.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ca91b54bcb7faaec493c29198cf223aaf05eba849249199c2c189a87b4a11b75; original global index 15836.
def localCycle00170 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 8 2, .gapLower 6 0]

-- Original cycle cde6b2909bf10f9899d87d3753cb71994908f84cacd74b7dd3414466b0b2202b; original global index 16080.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ce56a8d45e958b1cee469d43183fec6c216ca0d73694b6b60ace813577c86258; original global index 16120.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ce769270bc85b4c8ce269aa7670ee25c278d5591e0eb755470e9c732aba6fd38; original global index 16124.
def localCycle00173 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d0159fb17581b22406e50fd3706277a54eee4901bccfcf4bf8fd5272cb9f21d3; original global index 16240.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle d10b5e974155c4b5b17c83c58c87654042e18568792212af6e4a691ad1376fad; original global index 16323.
def localCycle00175 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle d193eeeb519f158bd8d21c79011c764ddf5a16e9bc7e99ccb51841cf9ea064d9; original global index 16355.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d1b13e1b64db1b8394324bcfb3ee7c2a81721b7e09dc93c361bb8b2b95a34882; original global index 16367.
def localCycle00177 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d1baa39dfeb3b76574d818615e98ee2e0e9c545263a538a9757e49a772cf11c1; original global index 16370.
def localCycle00178 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle d23cccd7d29d747367a15e7ebd2fb32d1c4e7d790bdc7f1b95e103fbde121aa7; original global index 16401.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .gapLower 6 1, .triangle 11 1, .gapLower 3 0]

-- Original cycle d26b9a21895436fe8709ae41350be2231b0a7d8453388d6ade5f94977240e0d1; original global index 16417.
def localCycle00180 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle d30166ec10fc45bc4551f4af29201c5aed3d6c2e183d24c6c8503c270c075700; original global index 16458.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 33 2, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle d3ad3314b376b33474923d612d8fe2fb58a3d15de4aa0015da0f1e9859778aea; original global index 16517.
def localCycle00182 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 4 2, .gapLower 6 0]

-- Original cycle d3dae0e91b30767e1d933f06a4b7b7b4538897b0373e1ae900bbbb0a690a02af; original global index 16535.
def localCycle00183 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 21 1, .triangle 32 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle d524de5e32394d746aa7de362a84ae7812123b509a09e845bc02a2c559ee2280; original global index 16630.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle d6bd0a924650da0127db804e4a4cd648b4dfd0bdbd684cbdac4e5835aabc5731; original global index 16764.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle d9366ccd444008b33fb973bbfb3f93b4727ee7c4361cd3213930408fd2717ab4; original global index 16971.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle da45d961ee821eb36ba290e8ed5667a2c86a5b32f954017e5ecde3828033b1c3; original global index 17052.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle df1346f6451aceb5ed0129e154981c77646392ee46d4a6ae238103e1adfba4e0; original global index 17438.
def localCycle00188 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 3 6, .distance 4 6, .distance 3 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 32 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle df23ba6864b98407cc200ed5ca64cb536efaf251d715ff19124ca20adab5c145; original global index 17441.
def localCycle00189 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 0]

-- Original cycle e0247aa42d2abc65d22cdbfe0f8c232971b6797cb3282d5b42ea438737d3c642; original global index 17521.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e08d7f6108cf77231a60e9a22cc13c4abb74fa96b69cdff723d24b3eb8b8a5a9; original global index 17560.
def localCycle00191 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 5, .triangle 24 1, .triangle 33 2, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle e17c8be99d5ee1a5014ea4ac79f10d7f7bf9f756778588b295f397cd0501917d; original global index 17634.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle e25130495b25685553f26cefd1a0a827f35d0dfd96057da0d7060857daa2179b; original global index 17697.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle e364b9883d887a508bcd08e81c7d82c29f58ea339c678d8a4739008e1df626df; original global index 17782.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00195 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e58e92bd26d47d0e3d14d9823c6e6d0ada361277595ff52cae387c470eee1ddc; original global index 17959.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle e5e8072d8e53179e6db8fe152b25b7f2f3e0698127c471513088b00e33a2c427; original global index 17988.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 18 2, .gapLower 6 4, .triangle 33 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .corridorLower 0 3, .thetaLower 0]

-- Original cycle e7ecbb8b5e7d8b3093a8843cb63659b168f8713f1947af58460240ebe8ca19cd; original global index 18137.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle ec531bd8bbe198f8bc49b356fca3e8064b095fb416a6380dac71a71e197a418f; original global index 18444.
def localCycle00199 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle edaa59782a5cf92afdf678556fffed9efda14929e9e94bfcbaf294b8633d382e; original global index 18555.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle edda44a36eeeb5021fc525846677393bfd065acdb2a3e45c468ee3a80f1bd696; original global index 18571.
def localCycle00201 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle ee77701b9fac87abf1a169c0f87b8e0a00b078a729da67e87cf46ecafd7f0c65; original global index 18612.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 32 1, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle ee8f68171479f1ad434680361ed39e4ec0501dc58b773d27a40b7d6f1188ce48; original global index 18617.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle eef12f8d126c68441bdc91416b8f498bb382b4dac22b39943369e8557083da86; original global index 18647.
def localCycle00204 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 1 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 24 1]

-- Original cycle eff0852b1468b45482d2046fbc67ef1b4c76949dcf4143bf79174b8067780d46; original global index 18724.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle f21423c39751033c992705f989a3d7e008ad9f9e29810a3f1d6015ca138e5d26; original global index 18878.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle f4ce35508929eff3f2995049725878e25c496d3acf448f89ef52969857e3ca89; original global index 19082.
def localCycle00207 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle f5006ecaefebedd333f24fb4f79fcce9e68995aa3ea5f0aa0ce2f55046db9b5b; original global index 19103.
def localCycle00208 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 2 5]
    constant := ![2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, true] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .gapLower 6 4, .triangle 30 1]

-- Original cycle f5623f9028f7c3e39240572d65bdd404a786694961e84994023a8625be68c281; original global index 19133.
def localCycle00209 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f89a85110fb1d63003b0d3c71f6e5e1e342289f83d0a52ff75343534500003c5; original global index 19389.
def localCycle00210 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle f8b1189b8cc6416dd43dfc7b57af4aab63d5f83308c5feac4ad12b13637c9f0b; original global index 19394.
def localCycle00211 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -3, 0, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f8ff6805347261315bd8fe541be955420b9eb8443e00a338c88b72f2ea9aaa8a; original global index 19419.
def localCycle00212 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 18 1]

-- Original cycle fb1b9057022d207441c8ac993b401eff5ee5ab0e082016bd4017ab7929d7278b; original global index 19599.
def localCycle00213 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0]

-- Original cycle fc2002a8e79135f2cf3bbe1b8095adc484bb97f3843ccc473b6f10d0ae266589; original global index 19687.
def localCycle00214 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fc3f7737d1391b84bc8b1aec0e1cad3d916e464880b0264c0a19f4614693aa28; original global index 19702.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 15 1, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle fd91511fbfe596cacd7e2aef249d506a27e3279bcdca99df1c7f770783805125; original global index 19819.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 10 1, .gapLower 3 0]

-- Original cycle fdaae97e0fb3ee161453df154d02128fa38d87b97b81d69b9b31b3044a4de0a6; original global index 19829.
def localCycle00217 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fe63291b0d3c4d1e061411412930ad371d380c2d372659478d54459062a35991; original global index 19887.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 2 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 5, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 13 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fef47a891689ad5c12d346067a8dc5e9abb7aa82456abc734a28e0435dce06fe; original global index 19934.
def localCycle00219 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle ffcd02b12386075cf49044efa9df022a4d3893a09f9ee612e8ff3218268ed9ae; original global index 20008.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Original cycle ffd26de008c5635c4771e798b732e0f5a1531fe93f6e0c81e72c3101bb9e99b7; original global index 20013.
def localCycle00221 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

def library : Library := fun id => if id < 111 then (if id < 55 then (if id < 27 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 20 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))) else (if id < 23 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))))) else (if id < 41 then (if id < 34 then (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 37 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))) else (if id < 48 then (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)))) else (if id < 51 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))))))) else (if id < 83 then (if id < 69 then (if id < 62 then (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)))) else (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))))) else (if id < 76 then (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))))) else (if id < 97 then (if id < 90 then (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))))) else (if id < 104 then (if id < 100 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))) else (if id < 107 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))))))) else (if id < 166 then (if id < 138 then (if id < 124 then (if id < 117 then (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))) else (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))))) else (if id < 131 then (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))))) else (if id < 152 then (if id < 145 then (if id < 141 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))))) else (if id < 159 then (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 157 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)))) else (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))))))) else (if id < 194 then (if id < 180 then (if id < 173 then (if id < 169 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 176 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))))) else (if id < 187 then (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 185 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))) else (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))))) else (if id < 208 then (if id < 201 then (if id < 197 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))) else (if id < 199 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none)) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)))) else (if id < 204 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none))) else (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))))) else (if id < 215 then (if id < 211 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))) else (if id < 213 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)))) else (if id < 218 then (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 168 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 256)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .low6 (![107, 211, 108, 140, 132, 30, 20, 24, 148, 213, 189, 153, 123, 44, 82, 208, 153, 123, 6, 105, 153, 202, 169, 153, 183, 49, 96, 153]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 257)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 136 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 258)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 4, 6, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 42 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 259)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 13 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 260)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 16 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 261)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 1 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 262)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .low6 (![139, 156, 15, 205, 72, 151, 20, 114, 118, 10, 43, 170, 123, 188, 174, 174, 174, 199, 116, 128, 70, 61, 38, 32, 117, 66, 0, 17]) }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 263)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 5, 6, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .low6 (![139, 156, 25, 201, 195, 79, 37, 41, 218, 129, 35, 180, 112, 18, 199, 115, 180, 199, 48, 28, 180, 200, 187, 180, 134, 101, 176, 180]) }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 264)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .low6 (![139, 156, 58, 93, 113, 111, 51, 161, 122, 11, 4, 126, 112, 144, 185, 174, 174, 199, 185, 181, 191, 65, 192, 89, 185, 78, 197, 57]) }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 265)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 160 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 266)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 52 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 267)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 91 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 268)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 138 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 269)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 34 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 270)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 190 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 271)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 209 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 272)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 2 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 273)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 94 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 274)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 141 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 275)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 154 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 276)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 109 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 277)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 50 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 278)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 4, 3, 5], ![0, 6, 1, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 158 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 279)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 4, 5, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 162 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 280)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 171 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 281)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![0, 6, 1, 4, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 95 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 282)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 196 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 283)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 207 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 284)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 36 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 285)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 45 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 286)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 67 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 287)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 73 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 288)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 21 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 289)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 184 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 290)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 4], ![0, 3, 5, 4, 2, 1]], proof := .tail 21 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 291)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 3, 6, 1, 4, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 142 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 292)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 193 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 293)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 3, 6, 4, 1, 2], ![0, 3, 5, 4, 2, 1]], proof := .tail 21 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 294)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 3, 4, 5, 2, 1]], proof := .tail 152 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 295)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 21 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 296)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 142 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 297)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 3, 4, 2, 1]], proof := .tail 21 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 298)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 173 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 299)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 216 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 300)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 1, 3, 4, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 131 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 301)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 2, 1]], proof := .tail 177 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 302)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![0, 6, 3, 1, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 221 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 303)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![0, 6, 3, 1, 4, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 7 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 304)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 168 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 305)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 2, 1]], proof := .tail 160 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 306)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 2, 1]], proof := .tail 52 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 307)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![0, 5, 1, 2, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 110 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 308)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![0, 5, 1, 2, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 103 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 309)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 31 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 310)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 145 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 311)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 71 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 312)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 137 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 313)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 164 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 314)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 121 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 315)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 155 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 316)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 22 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 317)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 14 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 318)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 77 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 319)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 88 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 320)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 97 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 321)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 220 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 322)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 215 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 323)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 68 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 324)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 99 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 325)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 130 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 326)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 36 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 327)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 219 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 328)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 90 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 329)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 210 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 330)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 331)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 332)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![0, 4, 5, 1, 6, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 147 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 333)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 2, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 56 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 334)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 1, 6, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 64 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 335)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 198 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 336)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 80 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 337)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 63 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 338)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 5, 6, 1, 2], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 203 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 339)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 5, 6, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 74 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 340)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 56 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 341)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![0, 6, 3, 4, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 186 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 342)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 3 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 343)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 163 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 344)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 40 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 345)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 2, 6], ![0, 4, 3, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 217 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 346)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 1, 6, 2], ![0, 4, 3, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 120 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 347)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 13 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 348)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .low6 (![139, 156, 15, 205, 212, 75, 8, 114, 118, 10, 43, 104, 60, 188, 174, 174, 104, 199, 116, 128, 104, 61, 38, 104, 117, 204, 85, 104]) }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 349)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 21 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 350)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 47 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 351)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![0, 5, 3, 6, 1, 2], ![0, 4, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 219 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 352)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .low6 (![143, 83, 5, 81, 150, 125, 133, 102, 26, 167, 84, 182, 100, 179, 167, 69, 29, 29, 167, 46, 26, 26, 53, 175, 175, 23, 106, 214]) }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 353)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 9 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 354)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 219 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 355)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 5, 6, 3, 1, 2], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 194 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 356)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 166 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 357)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 2, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 87 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 358)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![0, 4, 1, 2, 5, 6], ![0, 3, 2, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 19 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 359)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 5, 6], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 59 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 360)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 27 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 361)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 27 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 362)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 178 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 363)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 33 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 364)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 165 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 365)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 98 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 366)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 159 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 367)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 76 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 368)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 2, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 157 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 369)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 2, 1, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 370)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 1, 5, 2, 6], ![0, 3, 2, 1, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 119 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 371)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 2, 1, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 146 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 372)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 5, 6, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 62 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 373)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 5, 6, 2], ![0, 3, 2, 1, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 206 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 374)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 5, 6], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 55 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 375)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 149 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 376)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 135 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 377)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 1, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 2, 1, 4]], proof := .tail 172 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 378)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 6, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 54 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 379)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 2, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 127 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 380)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 2, 1, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 124 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 381)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 1, 5, 6], ![0, 3, 1, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 86 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 382)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 2, 5, 3, 6], ![0, 4, 1, 5, 3, 6], ![0, 4, 5, 1, 2, 6], ![0, 3, 2, 1, 6, 5], ![0, 3, 1, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 39 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 383)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (256 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 256 ≤ id.val) (hhigh : id.val < 384) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 256)) = true := by
  let j : Fin 128 := ⟨id.val - 256, by omega⟩
  have hsum : 256 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (256 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard002
