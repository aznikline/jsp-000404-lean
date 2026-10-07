import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard129
open N4R2RowDataReplay

-- Original cycle 010d1605e7d0885f1e3e0c6cb882b1d81060a4b40e69b61ef9c2c47899325d92; original global index 92.
def localCycle00000 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .gapLower 6 3, .triangle 11 1]

-- Original cycle 04b46cfd0f864bfc7eae2a0cbcfc11d73f63feda4faacb063de3d950b702de29; original global index 374.
def localCycle00001 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .triangle 18 2, .gapUpper 1 4]

-- Original cycle 04dd7e7b857d868b69c551de56f704ab72a01d1391153a6fef2a3b4224688339; original global index 391.
def localCycle00002 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 11 1]

-- Original cycle 06bf8d79ee3643eac2873f40357a04ad5eca36501303e041b461dcea566482e1; original global index 554.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 06dcb68afbce06992f7cde0c2d26d5c97f82d3a6f172dd0f7719ee448b86fbec; original global index 566.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 0765bce9a8fbba894c1460bbd4b6d5eed8691b7cb2e65496ca1d7529fbbd6689; original global index 610.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0a16ca50c753fd53877dc2825c9bc875223dc809acd4b4e25125692f18b5abf1; original global index 813.
def localCycle00006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 11 2, .triangle 13 1]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00007 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0d11ac722f87d6f4119998afc450a5c087b6d793b2e398f3d0548a14afdc705a; original global index 1037.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1146913eae8a78339f36ee2a62a9ba07ab72e33fdfde9ffd903907383ecff1f0; original global index 1373.
def localCycle00009 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 13 1]

-- Original cycle 1288de99ec42e1623e8e2c4960ffbb649cca1e29468aa1b24cbb138e821faa14; original global index 1469.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 141a0d51303a361c62612c38fa8615dcc1b47f01dcf4fb0f339694c26431c50c; original global index 1587.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1a391bb1f9ae345c99abc9b0cc9b75075eeafdcc346b8d0623852adce9eade63; original global index 2050.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 1bc26e8c986b59c5d9a3c364c6347fcc795eea2679128aeff8e9c3a217f5e370; original global index 2146.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 1f9e4515fc882549a911b52fd1cc9aa94b1ba3ed7665378863ec120c7edc4819; original global index 2434.
def localCycle00014 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 8 1, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 217cbe4bdc42584a4e190d81e1db49d06631361b0480f9601bb8fb1110f0242f; original global index 2565.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 21ae42f11dcf9f4a52bb1ec064a10c914f0e47e260806bf7711d75e0b0195f11; original global index 2579.
def localCycle00016 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 224b990c59b6c6c22ae882a221839dba02d578276bba69f6dd79bead7c902af1; original global index 2627.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 2387bef8188e1e58938b32a1a0160d753e4a11061d963521f5b4801e240eb09b; original global index 2725.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, true] }
  origin := ![.triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 251e0ca10ff9d9bf07708a17453c90398ae04127b4fc3d6c1a12f9b1221254bb; original global index 2853.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 26e025cdd138ca45021e4160bd0af9054d7696fbaf4c49abd8dd29dc395e3d31; original global index 2976.
def localCycle00020 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 2b419815bf56d904a622de858e2e9a2b9e6dc0bbb809466159c17c3bf891bc7a; original global index 3303.
def localCycle00021 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 32c5c30cef978e62de37ffab84041d99dfb430b9ede71345147778ad8c8af48f; original global index 3888.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 32f516069c9f2686d8b10730337c57c9f986c3b29ac711d3bd1ed78a125db6b7; original global index 3904.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle 36050ed86f902da8ec49c2f33cd6d515018a975a4ab37b9bfc6021d005acc4f9; original global index 4147.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 39589a65d8fc6e1d17799005bb19e808097a299cb02d50bd449e99473284da9a; original global index 4415.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 3b09193a41b0c3465b4dfa9573b619515e4820a4cd8797c70ef6319a61d814f1; original global index 4560.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 3dc55e1dcd3f1f2b9316350e702e64a65f7953465e3260943991d81e955c1af1; original global index 4782.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 4276979882fd9a0eb778c13b40ee24659d1efcfa6f0a72ee049fc20a67c96691; original global index 5123.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 42db32180f6a395f8a2d8ffc8f4a0a16b6c378591ea2bbee4008de5183819c33; original global index 5146.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 440a136b2331bac47f0f087a9ca769e90b0dd078f909cfcf294928e01f34143d; original global index 5266.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 450f9cce64ba46069d986a2044e647694773eda761435ad3de5eb0214e50a026; original global index 5342.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 46dcf14868f9d8f896cf88f1da0166aa5917bdd40f660be3604ab35a75fb369a; original global index 5493.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 4967b209ab89732a4122db95a6362eb2c4ee4158fb3c560177ee4001774f158e; original global index 5687.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4b5e8a36d5251fade1a3012390ea700792e30bf15117fad55e61c09a3fc402e4; original global index 5839.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4b8cea001e50e72d077336b7548ee83293ee966b7472feea02cebf3123d8cd87; original global index 5861.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 4eb5996c08250868c000c1e2601286c1b3736a2c84c08544ba0e332a0030b38a; original global index 6118.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 4fa54cf163346e2609f0e42d4380fdd75d10b5cfd8f7c95ebf8e08c833d50d5b; original global index 6184.
def localCycle00037 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 0 2, .triangle 8 0, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 52b8598a3c7bcc409b449e30c9968ece43a67bf1d164e7476070afc57d7e9ad2; original global index 6432.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 531dfcd80b106d6f21459935a614e21fdeabf0dc9e310232fdea4f7890606182; original global index 6467.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 532d3829197547293a1b44a69c741c222419b9314436ce5666a3088752d3fa6d; original global index 6473.
def localCycle00040 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 27 0, .triangle 32 1, .gapUpper 4 1, .triangle 16 1]

-- Original cycle 560b7073367c4e131343746c20014a844a1a046f36470becb204a3ad37e1c28f; original global index 6674.
def localCycle00041 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 18 1, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 566b209a0e4501cb4a4550b02c113b05e6f1909bec8e32f9df33dabf571d4297; original global index 6701.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5741b8513d0fad2cd330f6e0b815ed957a94fc069cc3657c55955a27b5bb330e; original global index 6761.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 5f362bbcfd88c7c1ab16d9b497216b0f941ebbc5fbaddcb6c7445cf8010cdae9; original global index 7413.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 603b2ec755127185ffe1ba616adf093467586594dade9699f903127ace474afe; original global index 7496.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 6077ef7c2608136a85fb8bed919234722c47099fbd6f377c974d1ecfac76b4ae; original global index 7513.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 6164581f0d444335e855f0f7361034751a0366327037126d3a903fa0da1ced3a; original global index 7595.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 61dc1c071e1a54f4dac03acc3fac05b7371cce883c930424fbe5f4d9c5174728; original global index 7638.
def localCycle00049 : Cycle where
  length := 13
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 6444200d60ee600b14ecd413ea40b98b8da1ddad91ff8fd1b4b5e3d533234cef; original global index 7810.
def localCycle00050 : Cycle where
  length := 13
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 652172eb6ed5f40aaa0e6b0105ac9f67f7b5098e54c8c1fe8d6c0f23d86fa99d; original global index 7869.
def localCycle00051 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 2, .gapUpper 3 4, .gapLower 6 4, .triangle 8 0]

-- Original cycle 65f4bd27b48402ed575e0566eb4e297d12f96aa7da27dc12b372289b70b95460; original global index 7934.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 66d0ac321616dc1a1417ece3d22e76e4b6172f3fd96b0deef047668795fda2ab; original global index 7988.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 67c2b64a537a3b7e74bdcbffa4ef37f86658e2001a6f01cbd650fd50804a70b6; original global index 8059.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6954bac03a2f054554c2b09cc02b389fa96d645771463cb0438df8230fefb55b; original global index 8193.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3]

-- Original cycle 6b81da148a465d756be0ca822eaa684485761d6b26553fd049354388d8fab72e; original global index 8368.
def localCycle00056 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 6bb667de5da69b2cbecf8c270a466d77a4a8ee607b987f47fa86d567b7dedbfd; original global index 8384.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6c1a7d9b914f18685b95147306809781411ac2128ecedf44471458f65f79bc41; original global index 8425.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6d160d2e9c82f2eddbea0879d39aa982555c541769cad5c2a0cfa90fd3538764; original global index 8483.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 0, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 7392202e6d87dba69c029b881985fbb851cda3df6cf8d8385c2c8712d7e415c6; original global index 8960.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 74f24f05dab9575543210bf62e0ea600646f1f1448f1485f7c22666d8e9f683d; original global index 9062.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 752fe3ec52d620a9420f76fcdcd3e129cc1853855fbae917388cb5d95d4a5e40; original global index 9080.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 76c243325475bee90eb864249e4c11052b1578b97375462166cda6bfca8063a6; original global index 9191.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 770436c47bf3b88bd9e24dfa79cf37df27df81d0e7da5a48d2254144e5ebe238; original global index 9213.
def localCycle00064 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .triangle 18 2, .gapUpper 1 4]

-- Original cycle 77bde39797849acd10cf65765c5b7a4b6c777b2d7f175a6e14a5851555fda3f7; original global index 9263.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 799091944c0d4180e9bacd6ebfd5fe41ac6321633e7ab2fa08a3172fc4c1985e; original global index 9404.
def localCycle00066 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 79e0c2a1076d94eff68a5fea8a7e6dd99c8462bf0a10f4907fba59d90ec6f9ad; original global index 9426.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7b8c42f1bf5264b89ef563c0f5f651bc4eb8d45ad705715e4da4fdb7ca760798; original global index 9561.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 8 0, .gapLower 6 2, .triangle 24 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 7c7490356def3517351df4c54004c9eb3a152298e1c4e16a6e0575247c77032d; original global index 9631.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 7d5f9b57e64d728a49530a8363855abd638e30701a181d1d6f9c007647600185; original global index 9718.
def localCycle00070 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 7d7860e877a3d6df0c2a2c73e562c61b2db0ba4f2b7e75ac292a009dfc79a942; original global index 9729.
def localCycle00071 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 8 2, .triangle 11 1]

-- Original cycle 7dc0437804ca373ab1c1a893b1f11fe10502969fec4bcc8c36341e358e336465; original global index 9762.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 7e05088ba8411fac2e5f9ee2d68a47e4af4f3b445d40e245d4a1a411f7304e83; original global index 9786.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7e172cde22bac407336eda221e9edb2c14906acbc6001aee29b080de02d4423a; original global index 9794.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 7e5d957ad83f3c6f02f128e1b2635929dd11d7d36129e51e1e41c4fc6fffc1b1; original global index 9815.
def localCycle00075 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 7ee90ee14ff66d2993b1211175dfdd35a3d2bec4f959b17fac254fd7e8b0518d; original global index 9854.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 81550e999dda738b5c51e001d02570be8e3b393f8a9b7ec7814c53bdc0b4912a; original global index 10045.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 82cedc5c648bf4c6bfaf49ea00abaa657ec3307fde69583e1be094a63b58ffc8; original global index 10146.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 5 3, .triangle 3 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8595923d5d85993aff1e51790c1e0292423a8d38212a0e2ae38dbddb8b3e9937; original global index 10367.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8aaa7b12161b34a128f5c581fe6dd11fc2ee818722d71dd058a187e9205d4d7a; original global index 10742.
def localCycle00080 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 8eff201f6665cdceaadcd0368c6aa9e7e7b301ed8fd167fe1e9c8f98aa52aa4c; original global index 11063.
def localCycle00081 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 9293dd3b53a59cfc038b1e73800fec37158132145a04f1aef29d8c895018a862; original global index 11356.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 92f8d2a7ec5a7f6aa5319d58ee3c7473e1ef84df71818dcec953a896123d3fd1; original global index 11391.
def localCycle00083 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle 940acb6dc1c83a35ed3af70a27e6cdd9b2034b158f245ecc9f5ce98bf1499648; original global index 11485.
def localCycle00084 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 8 1, .triangle 5 0, .triangle 15 0, .triangle 16 0, .corridorLower 2 4, .thetaLower 2]

-- Original cycle 96987972e3d8fdcb80175b35422f67f89375ac487371a56e558bfd1290ae82aa; original global index 11711.
def localCycle00085 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 99af3cec85d80c528da0d83b8fafb1e4450dabc9054cc47afccca171943b4fe2; original global index 11933.
def localCycle00086 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 99f26c133159fcb82c3e58ccbcfacb8596f67304edc2bd5bf8fe2630aa7e3d2b; original global index 11950.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 8 1, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 9b15ba711f27f5234bd6565afd6ea320faf25a03b3c5982fd35fa3a99d217e90; original global index 12056.
def localCycle00088 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 9bef5eaf3a6461265f579f3cd319a056604b5396066a27a08b752b5a3efdaace; original global index 12127.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9cdb6af4496a11cb8bddc5129a3af47e7e7d6d2f4672ac142e5ecc14eaa55999; original global index 12200.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 9d676743d4f6bbb339fa13fb4a1dd93490540ca8f77118a4e49d2a721b1f48ad; original global index 12242.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9ebd2f642ff3a7a38eb9c732988f9cd0bb1b0e389a50c8009e2abeaf33bec107; original global index 12358.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a11461233dc4006333dd0931e75478c0926269dc69d38237665141254c8a2796; original global index 12527.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a140b1d76f7ee24d4b6d22836b81c5011cddba96d05aabda0b564a302c0cf928; original global index 12538.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a14cd180501dc6436813ae5976e508dae32398fbcb0fe7d606d3b5f0da5437eb; original global index 12542.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a31afbc85d6c0102f69dc4536d00b606cb72ecfb10c0f131b69e1e8ca6b36e15; original global index 12682.
def localCycle00096 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a40402dde71e85af6ba87c65c5e6f03120f064eca7e43d0058aeb1afd7383465; original global index 12752.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a446f1a5e2c81eb285ea38bbe41f7ffebd80d11b56f1c22ceb6b12b2f604c79b; original global index 12767.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a4fa15093a13e46afaf8b26e1282acab8f87d7d588ee0c392b0e84b564adfcee; original global index 12820.
def localCycle00099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle a569b568d233d55cc77905dc054be430a885f26920b7acf3660a3f8890256864; original global index 12851.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle a7173c611f3c950ca583aed29bd006d03d254dafa4d5334cfa686fdc7a940fe9; original global index 12989.
def localCycle00101 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Original cycle a811e52c743462052c0d849f77d7e9a9264272dd93017707ded69d395923be6b; original global index 13089.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a81fab8a33fc036313c3541005dcd5028c2e61ca6bcc0a857706d4c277398afa; original global index 13092.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle a95a37ecdedee0105426aa6b91b4632ef9bd0e651a1a1e20cf66ca566c42afe0; original global index 13186.
def localCycle00104 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle a9854fd6829e729c9d19775ecdb167b29916973c6a55ec02d3c2559653f837db; original global index 13196.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ac3bf4c00cd4731ecc41409427980efa7f213b1e04cdd7aa4c414a38456b8e62; original global index 13426.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .triangle 6 0, .triangle 0 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle ae90eba61d4dac8c176504a78f4840f7e8fbd3f2be6039bf2d2c4d1d72e872c9; original global index 13626.
def localCycle00108 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle aea0ba84e05bb5afd639efdf13b7b70f88df7c51f977c3011e85e41938ff4231; original global index 13630.
def localCycle00109 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle afbfb00861ad5da8fead6d6a2a3d27d717204c6022b31d0a75bcb824f9ff6e4b; original global index 13729.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b179f5057aabf83c5b44df1cf7eeec89571d94cf2b04dcb73218db92603733f8; original global index 13872.
def localCycle00111 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b51f7c3c4982140d7f7cd423d40272d5f1499f41966f5576ea2e3efd3824c8f1; original global index 14154.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b659ed63cb1b02564354cbc3c9b6293ffe645a22aef5be8718698ea8a1211402; original global index 14251.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b73376aa331c64a55bcbe65e00994a4acd676ac0328c089a1a8b603a2f105ac6; original global index 14303.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b7c37d5e162be7246f34681d48534223763f8fe8b432a07bae45e9a2c36dcffa; original global index 14340.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b897357aa416fe4e607fa5c3bc556f8297cce6be95f41557e206c957843db44b; original global index 14403.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b95706ae5a40886232da44e0f638d65b8be8117430be525f72e9117e5c3d0e1e; original global index 14461.
def localCycle00117 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Original cycle ba0eccfebc90dff06eb9843ae6836ea36528bfaaef9e63749e16121a043981d3; original global index 14528.
def localCycle00118 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle ba75cf230adfcea4ea989b6f7e4568f574087625187d5148331542e1331b8cbc; original global index 14561.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bc4a90008d6c9956544bd1a171d13f453baa41f5a68e6e1b99dbcc148e63e4f7; original global index 14697.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle bea95355e525ccc4f2b7b3afb40d7299eaef9e40d188f5801087c91b9e103cda; original global index 14875.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle c0b69f3ebe3c3fd5fc62dcb63b2bfb636f43e0ddca2317cabfa293a631d62605; original global index 15048.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c1286a123307a1e98dccc97a2ee9bf8cfcb09a1b32c1252e8bc6a2797c03f68b; original global index 15078.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c1554981436a227a3d23a217788b7f6b1ae3c008369a83654a596ba15a390697; original global index 15095.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c25203ee2b6c449849da7a0c90eda229fab994d217806cd995087f5c791c0495; original global index 15173.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c2edcba25dead2311ffc97fe100c2a1bd379eaaa3347106db935a489c0ddeb73; original global index 15212.
def localCycle00126 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c497ad5125fccc60f639f129f53ce1da188495187bd851c2d67443649588513b; original global index 15331.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 8 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c6e23e5e0a73bffcd07076acda1d649c738b5d0481767bede8f5af2d9ba21479; original global index 15520.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c797e5a0fb02de15c835b7b33db7d60202cb32434ce97cb36abecfa28edcb6c7; original global index 15576.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c7b8ab3d74e0b3ddb386ada6fe7116fffb3dd2ad72905d791c119541b62f67c1; original global index 15589.
def localCycle00130 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 27 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle cb5e6872d88aad9b4545c4a4d6b165e6eda8271b33ece8f4e7ba60fefe1b9a9e; original global index 15887.
def localCycle00131 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ccd34bdac46e5a5bed5e090f922a7ccb8ffe1984ecdce8dcfe43e29ce88a9be6; original global index 16006.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true] }
  origin := ![.triangle 0 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle cd5a89205808c0ba6c6f1121ca8965b535fb32fd5e34d63dfb4f1d08b8e2d215; original global index 16051.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle cee467fb13270fd9cec5f6ba80c5f762f16a97cb692e16099af2a661bf67f7b2; original global index 16148.
def localCycle00134 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 9 2, .gapUpper 4 4, .gapLower 6 5, .triangle 11 0]

-- Original cycle cef9b37065b2084193d545f5a4bed95d7934bd32e07bbf622f9e193631bb97b6; original global index 16150.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d01e067f9cdb15d33ea617741fd303342c35da473c0d328e5bcf46769855a9d5; original global index 16246.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle d32cae771064c5cd1d0fb8621fd98956496f4013c39a812353f2d93263e4d99d; original global index 16473.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d3678c49a993487dcb670e8bf518126da40714c5a0f39560653dbdb33084f0e4; original global index 16490.
def localCycle00138 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 13 1]

-- Original cycle d36d8f963e7dcb739e611ab952a78d859843fcc640f9fa168c94e20d46822150; original global index 16492.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 0 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d5272afa4c41ff0a5c602167d878382eaa8969d1605a508c8a325fc5be44fddc; original global index 16631.
def localCycle00140 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d6880f389683255bdb4afea9b9cfe9d6f10354b58b087a8c2555101ede6a7d42; original global index 16747.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d91068ded6e9e352b5b93466a78f48002bf69f957f16f53cc504703ada4588da; original global index 16955.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle db4b360295426a9635cfabb2c8f99ad0e07e19fedf7f916b2c5ae2207811ba08; original global index 17143.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle dbc12c2289f800a16b121d9f0020929965be44f0377cf98cb28a3d4eac57f947; original global index 17174.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dcc51955f456d92d34836d9b800c450c550609b7dbeaf14c92c5d1e4ae097a6e; original global index 17249.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dd847097386f0228b04b000f27fcb2dc8f97c4cebc9b12369dfa913f3eb6ff5b; original global index 17318.
def localCycle00146 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e028d93cd204bff7cc0cc8813ebd336c21ab78735b3118ce93241833277080bd; original global index 17522.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e6d3b93f6ff0806f6be738086c3d80985d7f1f8cd5f36a1fbac237a7bef3b9aa; original global index 18061.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true] }
  origin := ![.triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle e7ebec6e9c76d00cc5ab8a8e12f59ed6fe993d9311a8e44247f915b85656c1e3; original global index 18136.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e97e9e54b81cae1cfc581b44e5ed116ba60cd0a79b9a11ca773fa5cc79c6be19; original global index 18247.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle ed60743e8c912314390ad0481374a165a85568bae045cd70b07e8ea8530f2b32; original global index 18530.
def localCycle00151 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle ed77e966dfb64c8194aa2b5d10bb19fb2d47d94ee73c836dab79345d2fc7d5d7; original global index 18536.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle efb255850253d4ef394db25ad2d95e439d9dafe16c3ec4b6e045a82e88913d39; original global index 18697.
def localCycle00153 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle f33690ed62cd9ee0159429a3bd0d5c9ff518317a7a4f57cb32a89ffa11031267; original global index 18967.
def localCycle00154 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0]

-- Original cycle f37c1ac923fbf40ed333e428a50182540cd6740579c45b8f293d7920069509d0; original global index 18994.
def localCycle00155 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle f54d1d17c8edbb68e89c66565db1c899d1a66fde6668e5ceca5a9cb3341155d3; original global index 19119.
def localCycle00156 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 8 0, .gapLower 6 2, .triangle 24 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle f6db57e3281c10222806f449b76493564c6df03ac1aa77e5bc623d0843b06d05; original global index 19255.
def localCycle00157 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .triangle 21 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f8038d894bcd1008d862df0ff2f9c2d5d1a52f696572c28de07e46dde1bb8bd5; original global index 19332.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Original cycle f8084dd5b130f74ee1f3f464b27f98a39c36f02ddd43d2b849f70fbc2a45f066; original global index 19334.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle f8bad1c038dcd4f58202a5d47cf4596332a8c2f034403de149cd1903df783d20; original global index 19398.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f8f87d8e36e613ce2937785b8a92840c6fe410b2948c3606ee3b2832b8958fb8; original global index 19415.
def localCycle00161 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle f99ece6ca02db51cc335d67d5ce7b6c268e6c31b66360fc503fe21fb451535f0; original global index 19460.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle fa1571deca2076906f4fbee0df14a9270437ff65ceb961f652c7925c7f66f009; original global index 19500.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle fbe64f28c3bee9b64773c4c96fdfafc66640644af15c69af22a498b5d4485735; original global index 19664.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Original cycle fd8adfc371e62121376aaa6dd2773d5ba69a2276c986000dab4c2445679c4e8d; original global index 19815.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fedbe70c6f5347552fe8d0c72969aaa1b48e926ad147a7262e45254c73bbb5e8; original global index 19928.
def localCycle00166 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ff262d59cf7a11650ee7cdcdb485ff8747aa757ddf8c83e057db4e01492612ae; original global index 19950.
def localCycle00167 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

def library : Library := fun id => if id < 84 then (if id < 42 then (if id < 21 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))))) else (if id < 31 then (if id < 26 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))))) else (if id < 36 then (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))))) else (if id < 63 then (if id < 52 then (if id < 47 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))) else (if id < 57 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))))) else (if id < 73 then (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))))) else (if id < 78 then (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))))) else (if id < 126 then (if id < 105 then (if id < 94 then (if id < 89 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))))) else (if id < 99 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))) else (if id < 102 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))) else (if id < 115 then (if id < 110 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 120 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))))))) else (if id < 147 then (if id < 136 then (if id < 131 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))) else (if id < 141 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))))) else (if id < 157 then (if id < 152 then (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))) else (if id < 162 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)))) else (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 4, 0, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 126 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16512)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 4, 0, 3, 5], ![1, 6, 4, 0, 2, 5], ![6, 1, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 154 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16513)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 4, 0, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 74 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16514)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 4, 0, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 18 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16515)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 144 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16516)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 146 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16517)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 2, 6, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 0, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 150 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16518)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 2, 6, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 4, 0, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 150 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16519)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 143 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16520)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 4, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 161 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16521)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 122 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16522)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 6, 4, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 159 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16523)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 4, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 122 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16524)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 6, 4, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 159 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16525)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 4, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 69 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16526)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 4, 0, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 99 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16527)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 4, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 158 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16528)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 4, 0, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 18 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16529)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 101 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16530)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 52 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16531)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 2, 6, 3, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 0, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 56 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16532)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 2, 6, 3, 1, 5], ![4, 2, 6, 3, 0, 5], ![4, 1, 0, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 164 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16533)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 166 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16534)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![4, 2, 6, 3, 0, 5], ![4, 1, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 166 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16535)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![4, 6, 2, 3, 0, 5], ![4, 6, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 167 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16536)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 6, 0, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 85 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16537)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![4, 2, 6, 3, 0, 5], ![4, 1, 6, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 85 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16538)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![4, 6, 2, 3, 0, 5], ![4, 6, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 25 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16539)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![6, 4, 2, 3, 0, 5], ![4, 6, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 81 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16540)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![6, 4, 2, 3, 0, 5], ![6, 4, 1, 0, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 159 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16541)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![6, 4, 2, 3, 0, 5], ![6, 4, 1, 0, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 148 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16542)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 34 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16543)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 120 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16544)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .tail 163 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16545)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .tail 28 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16546)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .tail 28 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16547)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 46 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16548)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 46 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16549)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 6, 0, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 113 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16550)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 3, 0, 4, 5], ![1, 6, 2, 0, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 62 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16551)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 6, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 113 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16552)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 3, 0, 4, 5], ![1, 6, 2, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 62 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16553)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 3, 0, 4, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 133 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16554)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 3, 0, 4, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 45 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16555)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![97, 77, 70, 60, 147, 7, 92, 89, 123, 110, 110, 110, 110, 30, 43, 43, 43, 43, 107, 27, 137, 140, 47, 152, 61, 162, 106, 29]) }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16556)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 149 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16557)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .tail 15 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16558)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .tail 104 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16559)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .tail 98 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16560)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 8 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16561)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 8 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16562)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 0, 4, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 151 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16563)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 105 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16564)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 105 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16565)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 0, 4, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 102 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16566)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![6, 3, 2, 4, 0, 5], ![3, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 49 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16567)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![6, 3, 2, 4, 0, 5], ![6, 3, 1, 0, 4, 5], ![6, 2, 1, 0, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 40 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16568)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![97, 77, 70, 75, 111, 7, 131, 89, 123, 110, 129, 24, 110, 30, 43, 43, 43, 43, 107, 129, 137, 141, 47, 152, 127, 82, 94, 3]) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16569)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 14 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16570)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![97, 77, 70, 75, 39, 7, 108, 89, 123, 110, 110, 110, 110, 30, 43, 43, 43, 43, 107, 27, 137, 93, 47, 152, 91, 48, 139, 11]) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16571)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 103 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16572)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 119 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16573)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 109 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16574)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 53 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16575)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 20 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16576)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![97, 77, 70, 75, 71, 6, 95, 89, 123, 110, 51, 134, 110, 30, 43, 43, 43, 43, 107, 51, 134, 157, 0, 83, 87, 138, 51, 134]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16577)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 84 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16578)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 16 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16579)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![97, 77, 70, 75, 71, 6, 121, 89, 123, 110, 51, 134, 110, 30, 43, 43, 43, 43, 107, 51, 134, 93, 0, 83, 72, 138, 51, 59]) }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16580)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![4, 3, 2, 6, 0, 5], ![3, 4, 1, 0, 6, 5], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 96 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16581)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 3, 2, 6, 1, 5], ![4, 3, 2, 6, 0, 5], ![4, 3, 1, 0, 6, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 41 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16582)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low6 (![54, 112, 156, 64, 36, 7, 90, 79, 115, 116, 142, 142, 142, 37, 5, 160, 160, 160, 80, 68, 68, 68, 44, 145, 1, 67, 76, 38]) }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16583)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 135 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16584)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 42 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16585)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 125 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16586)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 10 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16587)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 88 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16588)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 153 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16589)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 13 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16590)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 19 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16591)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 153 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16592)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 4, 3]], proof := .tail 13 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16593)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 33 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16594)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 55 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16595)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 10 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16596)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 4, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 26 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16597)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 66 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16598)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 4, 0, 3]], proof := .tail 13 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16599)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 6, 4, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 0, 3]], proof := .tail 35 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16600)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 6, 4, 2, 0, 5], ![3, 6, 4, 1, 0, 5], ![2, 1, 0, 6, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 0, 3]], proof := .tail 23 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16601)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 113 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16602)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 113 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16603)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 12 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16604)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 113 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16605)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 12 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16606)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 50 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16607)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 65 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16608)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 58 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16609)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 55 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16610)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 32 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16611)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 26 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16612)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![6, 3, 2, 4, 0, 5], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 26 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16613)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![6, 3, 2, 4, 0, 5], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 4 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16614)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 114 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16615)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 100 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16616)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 6, 4, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 31 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16617)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![3, 6, 4, 2, 0, 5], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 23 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16618)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![6, 3, 4, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 130 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16619)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![6, 3, 4, 2, 0, 5], ![3, 6, 4, 1, 0, 5], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 23 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16620)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 4, 2, 1, 5], ![6, 3, 4, 2, 0, 5], ![6, 3, 4, 1, 0, 5], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16621)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 53 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16622)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 21 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16623)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low6 (![54, 112, 156, 64, 2, 6, 86, 79, 115, 116, 142, 134, 142, 37, 5, 160, 160, 160, 80, 68, 134, 68, 44, 134, 1, 9, 57, 134]) }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16624)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 63 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16625)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 118 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16626)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 153 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16627)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![4, 3, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 78 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16628)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![4, 3, 2, 6, 0, 5], ![4, 3, 1, 6, 0, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .tail 17 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16629)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 13 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16630)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![4, 3, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 96 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16631)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 3, 6, 2, 1, 5], ![4, 3, 6, 2, 0, 5], ![4, 3, 6, 1, 0, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 155 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16632)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 124 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16633)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 128 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16634)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 6, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 22 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16635)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 73 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16636)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 165 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16637)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 136 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16638)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 4, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 117 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16639)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (16512 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 16512 ≤ id.val) (hhigh : id.val < 16640) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 16512)) = true := by
  let j : Fin 128 := ⟨id.val - 16512, by omega⟩
  have hsum : 16512 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (16512 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard129
