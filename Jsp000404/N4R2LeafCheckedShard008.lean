import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard008
open N4R2RowDataReplay

-- Original cycle 00f24d6804f7efa45f7a88b8da931daa6507f9ee1f2dd8fb700e9aad99a0a4bf; original global index 80.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0207346ddf14a07e407cbe2ccb6f7a03456775b897c478cfd8f68ae471db1098; original global index 165.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 02385431a2da74b5f10bad89e72b2feee7d3433459c0ead125643796df711d31; original global index 176.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 028affb3f5acfea66d1d66bc106480d80231429817b712050e7a255b52d27851; original global index 199.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0332080cd4dc26421902a46cd3f555023760b6de7b244bd32beaba216b6b5fd8; original global index 256.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 03ebbf996e97d765a690b240d1c3b23246539a91837f2d1125065be63dc8e630; original global index 310.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 04347885b6b52f7b66257bbfdc9d9d39b182904d802afd1acd006e1014cf2a41; original global index 330.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 29 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 044c2ed28de3b147f1baf06632b791af9c87c8001a3016c02379276a3ce704b5; original global index 337.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 04d8f923d58b7ffa697b506d33fa212dba581c94108356258a2e4b8260adce29; original global index 389.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 058cc8156ed34defd873653e19f4ad3c0aa380914f96f008ce128d6d17484805; original global index 457.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 068af6aca05c37372eef42ad5010a275cf868b92ff70973645116c7926f35e86; original global index 541.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 06c989158a5150f7558784821af980e859c1414fb01aa326b7a672ac7d448ac5; original global index 558.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 09bc334f5b0be602c14ba994addc4fbb6ba65d903e1b9130769d332947684d0b; original global index 779.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0a70aa4a626e99e54055775a8398138ef05a95a3b07dfd7ba412f9ebbebb1d40; original global index 830.
def localCycle00013 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0abf8f2921ac57f4e063dd0d96e656789e0d32530655b94404d0e847cabadfcf; original global index 858.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 0aec698d35f05de61f2a66e02f5abeee3251961358a462214fa6fdbbb57146c2; original global index 874.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 0b28a83c3b72e71c5cdbe76164a0f4f1bfc8542d6f7843a975b1deb52d7e8cfc; original global index 893.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00017 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0eafbbeb0cce4c0d261c59ad3f08792dd286406401635b8bd01bf64b9bf73244; original global index 1161.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 0ef59f86de0a098f6c53c80fb80a6101cab42fe48f891220a38fd7e64b1d7ad1; original global index 1183.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 0f86b94dc2536418475ecbf1688f47b86fac5bb1e75d728b63fe6b4f674c4df1; original global index 1236.
def localCycle00020 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 6, .distance 0 2, .theta 2]
    constant := ![3, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .gapLower 6 2, .triangle 8 1, .gapLower 2 0]

-- Original cycle 0fa1f2ee161a79bc4aaf42a1f2080841299d74c0639d3b168ae1e67c632766eb; original global index 1244.
def localCycle00021 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 21 1, .triangle 27 0, .triangle 5 0, .triangle 0 1]

-- Original cycle 101155bd35c1980e56c96cfdba494c8e05e2a54318e17a4d057e3c83ddd1cbaf; original global index 1285.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 101d55cceaf49bb900e9069f3378c54f945bce10ef1212a4180cb9cf3318e934; original global index 1290.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 3, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 10cc90e9880d25a98c377942f8239392065e2ba112f1f3304ae564241a8f85da; original global index 1346.
def localCycle00024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 23 1, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1]

-- Original cycle 118406cf0b953eb642ad469deb23a189be5589ae1bb04adfff91820712888d22; original global index 1397.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 146ef0860e08a6d1c0b0dd0a600805c15e4e5432d67dfafed6069d6ebc998ae0; original global index 1614.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 16c77ae6f83df1b2e15204fa4bd7137ea6e7b413ab57b2dca34e84b00864d53f; original global index 1788.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 1aad4aa533312627856b10b7cd412b0da506e90d808e2f1e925f48afb59b21bc; original global index 2075.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Original cycle 1ce35ca6175e49577be5ecb4d53bebd6a733c51f71cb3b13d2f1c5c55f6d295b; original global index 2225.
def localCycle00029 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 1e4fe6a9cc8df7cfd2da9ee01082df04f4827f256bd29f9d14e1ed5baeb901b3; original global index 2330.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 29 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 2019b05ea74275c267497c6c377a04a763331b0db67dc620b3245859697e3c9a; original global index 2464.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 214748dc8469ef49aa864dcfd593f045c16f15802c98f92da28af398079e91f2; original global index 2551.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle 222d98dde9d60665c368ab5dd33ecd0418d21d5f12b7683ec5fedf41701859d6; original global index 2617.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 236723c3785a413cb9edc83a3de10fe78453b5b1ffcbcc79f362dc9b55076af7; original global index 2716.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 250ac5197bbc443c13d28cebec3fe82d058e5d277a0c6adc0b5f5a6c4ed954c7; original global index 2846.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 2, .theta 2]
    constant := ![3, -1, 0, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 27 0, .gapLower 6 2, .triangle 8 1, .gapLower 2 0]

-- Original cycle 266ba7a899c0e65c4fbee916c0cf9e5b19a8d481065034ed84ebc5e6f61c2690; original global index 2948.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .triangle 23 1, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2691ea43d9c35d9289a4ce844cbeb5398bb3f23e06eb67629c58cb755eb1f748; original global index 2957.
def localCycle00037 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 6 4, .triangle 23 1]

-- Original cycle 26a94a28d16ad5cb236c771ffeeb1d8b39db1bd1e353bd7a64dd1f69c929e725; original global index 2963.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaLower 6]

-- Original cycle 26b27ae95dee3fb519ace12838922e922b94ba98c26c58d86adec0533f191112; original global index 2966.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 27cd2e574ff7bfd7e8835bb833662409678a173ca2814ab68f5ff6042899d251; original global index 3044.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 281f0ad69143efc1c6e5d51dab0c7949e1861941926e80a44edc97a24c1e2236; original global index 3067.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 28c000703fc1013632c10d2fedecc06e2ab773eae15d878e01a013f152d6ddc1; original global index 3119.
def localCycle00042 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 29e1077fa92ecdbe496159d5b0bd3e6bdba18f02c25ce2ad8794598745adb023; original global index 3196.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2a2757474f97970d9c1dd50b53ad0002e5540aa62ce3a984509acfe41b656a09; original global index 3213.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2be9f858277c2bc79d9d8cd8c612dbf897b3522c95682a5174625b0202dbd019; original global index 3359.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2c7675ad49e493d10a8312bad21cd1a08d6398f3892cbb13f2bf7d5920ad4c99; original global index 3397.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 4 6, .distance 1 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 1, .triangle 23 0, .triangle 16 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2c913cac3462ddd8bf1f2397fd073d76d7c372dee9226116fe1985df1907ed9e; original global index 3405.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 2f9325154510c519c1796e88ef7664f95c4b5a4716bba69d7cbe778725a06baf; original global index 3633.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 30a77b1fe521596c838e3080e1b528faff119ba22d147e6d4cb980fce1f48aa5; original global index 3712.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 30d95be31b548b6bcf3a1e70d9c533010997459b50cadf1e081ec475e33042c5; original global index 3726.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle 3110176ee00a7a75418a667a32b0de91efbbf3f5a5ba5742a45d78145454257e; original global index 3739.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3120eecef2d447cae13260310581fd9586d5e4383dc7e76ff5b5a443c9693fd7; original global index 3746.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 32464ce89d9c7ef196c1f93cbbe9779582ce45ea048e8d644881e89529a11e2d; original global index 3837.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 3376642a96131b9eeacd645104478b0d06b24e6cd9a6624bcaf042eb97c0c52d; original global index 3937.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3420e7fe322557af89b2b31b41d195b18f104c2f9325a6999d73d8ae5a20418c; original global index 3997.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 3614b713c007ad86c460a3f9adf668728fdfc21396d9e0a49294480dd83513fb; original global index 4153.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 388da610600a819ccf40ddf49849f58a10b1175fde0a6e038e68e92fd5754d38; original global index 4352.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 38d721e11610d21748237ab1d45dcde7e97bb450c9ba2068a65afc65fc6e571b; original global index 4376.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle 38da72ed28a1202f0866288761ef60b6d291f7db04fc0501d9da6d6d598c59a9; original global index 4377.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 393655b19280e35bb2f95eea8dd8ccfad106af15456e9d90907c7b97eeed583c; original global index 4402.
def localCycle00060 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 397856ce3ce4758bb088fa5a4ed112bf4a34529506332db07703760f9a61e28a; original global index 4429.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 39e1c7b8b50a2565e66cfab93bc21dae6c1100ca7508b7576d9a18bb06dda718; original global index 4464.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3a2a02d3c87fb9dfade9e8c8f9c578cfeeccfc8bd84af331feb93a83c23e9da9; original global index 4494.
def localCycle00063 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3b0c5932691456e2c190d0704bd07da9d456568bf2222ef0aa76b311d502b6a3; original global index 4562.
def localCycle00064 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3b40710867f142cefd96ba00574e57d5f38b99683a828f832b4ea37f199da966; original global index 4578.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 1, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 3b5082c20fbbffc5e95e89f9363a45e614553743850f17e722717bf0394a6a08; original global index 4584.
def localCycle00066 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3e1e1b0498fbd8894c743f7886ac980ef5d60c684ab3707e312838e11bf84923; original global index 4804.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle 3f435cb3f1ef4cea54ed7afe5b91f35bd35541e65f2eb7efb4345e4178f26a20; original global index 4887.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3fedc8ae132d3dbbbf50697d4ec1e21dd11054591010ecc11c722750feb8e338; original global index 4934.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 4007896e30b41ad49a517bb29a7fa85a377aea067678275aded96f686d5f9d62; original global index 4938.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 44e30eb2debab5cce9b2150bc31bf5d2ee05694821a095e24812fda2d2ae990f; original global index 5338.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 454266f25e90e8da6e5ef0ddf003a2cf02299f6a09439cccf7aba4f9d9ae5a96; original global index 5357.
def localCycle00072 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 46358cd9d03e22fcea1da8082af2c91f972ce1ee08a10d64678c496a6bf459ae; original global index 5434.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 46b85185a1c29db9c90cd265db9a0c688d9e12e80bedeb1ec0ebbab9d50d238b; original global index 5477.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -3, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 46c0427a1c2c8cb82e7947c9186fe27960323fb190d5d8a1ac4498792f1b6e8d; original global index 5482.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 47c53fad7653dcf286669560b5ef3561500b7ff9ddfb709b8fe3682b6de8a668; original global index 5561.
def localCycle00076 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 13 1]

-- Original cycle 485e1c97b27f10cae00a60380e6f5d8d3604a0005fcf7989700c86f8e375c609; original global index 5602.
def localCycle00077 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4908790bd9f63f310d2d6782cab1d92ddab49a384f35ef86ae13215eeaf850b2; original global index 5656.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 497e450be5c51598683e3cca61018e3983a54f203dc4cd4c89eac018f3ce110b; original global index 5697.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 4b5f358a6999669c211564fea0b2b3dc3fb1bbadf98938d2b1030cfd759797fc; original global index 5840.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 4d3619e3b46448c5b718eb4fed2a09cd3ebb6df7f6cbc6690d0430bc08881cf2; original global index 5995.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 4d46e0f7781c3f12b559eca2e2f1be026b20823ce4855645e26ccd2f9241d719; original global index 6000.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 18 1, .gapLower 6 3, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 4d8c3c14707fe9293d755bbddb4ca48f65a6432eaa04e2d117e7ad3b7f006e81; original global index 6022.
def localCycle00083 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4d8f114e029a8bb64d6fc581160427df5c7983a3325ad4d7b74500d69c860a7f; original global index 6023.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Original cycle 4f1f06ad5d101861d4f090dd1fb868e82d83a1d72c52b74bbc907896fd1dbd9f; original global index 6145.
def localCycle00085 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00086 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 500e918d2777721da7414b2f50ca59106ae992e333404ed0d7068c72c190ae7b; original global index 6214.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 5124431b0d45d04efac848543bbc1b92ea8b6df96efe440f81ccebbe3286ed5d; original global index 6303.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 4, .triangle 29 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 52a180397a1622026716a8806c41efd0937a448502e99bc52702fffe17fa3bf2; original global index 6421.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 52fe720db0de6ac99564b0e47ab0e36587c2b58fbc8fc3f0fff5488099b86d83; original global index 6461.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 2, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 545b05250bf931bdef23ddd7d12e1e3fae662d024540fde956cb631803853d07; original global index 6538.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 5840f72db73b96dd0cecca6a59e97813ef69c5237cae4e9ebd2e29c912516339; original global index 6847.
def localCycle00092 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 597e035c137e5e2ef593d40ea533f0780c81b4943ab83b83a46631e52fd85e4b; original global index 6952.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 597fc8888cc6a4239aeb54ff1d22d774bf9864e23faf4989d41b48b140b65000; original global index 6953.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 59e0d6317bdb989a12683a1e7fde4aa0d830fed07c7d643559a4e9dfa3c9fa1a; original global index 6991.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 5b0837ca7dd62e7b4cbcdfb7283d61037f557f6610c448f7baeb633290283c39; original global index 7083.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 5bb1af0ebad855f90b4d2ab002a903122e7a65a3b76952ea6415acdf08c5bafd; original global index 7129.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5c31ce1ff423067d7384dd5c5495594447031ed5d4d238b61b2d884f5c7a8fc4; original global index 7179.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 3, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5c687a825338fb77b6b46cccc35d77eff8ae88de1c0bdd0ed3fba1d015cdb404; original global index 7195.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5cacaae88eb7429a94ce2a287b1d81161b392ed323ee2de821922a15fbca4187; original global index 7211.
def localCycle00100 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 3]
    constant := ![2, -2, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 29 0, .gapLower 2 2, .gapUpper 3 2]

-- Original cycle 5ef60175d4515a8ffe414477a2698905a2fcef6976d3a6a17cca2ad950feeee9; original global index 7394.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5fc20b1bbf2861eca2b61126546ddea6a8c099bf754d4c55b5f758dd232b7dda; original global index 7461.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 6075cc38a81a1ff8e82803af846e037e2476bfcc13d1a3bfa614992881cbda42; original global index 7511.
def localCycle00103 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 61db8d3d829369fabf00de222bfceecd081181cc07c83a393565d26ab919e708; original global index 7637.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 620312acf1703c1197cc9619127a8c0e4c02bed2f2ece7008cf198d0d41e506c; original global index 7652.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 646cc90e41cb74878d523bc04066d78491e54024fb6015930f16b92bbe841c43; original global index 7819.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 647f019cadde0163eac5229ca90fb129af517e4a83b75a72cfb0d9438975cf6c; original global index 7831.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 65b2087ac4042fd13a5f27a819d96486784d4e4007b8c14e8f3205cda8aed05c; original global index 7909.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 66ff1897ddfeae1761ee5b7cf5f420775541a4fb44c7c987bd122aa05743c888; original global index 8001.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 683605d2ec60d315f48dbec691d954a60a830730e837565ebc743ffc231504fd; original global index 8102.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .triangle 18 1, .gapLower 6 3, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6904a0452e39b63142b011b2def09d5c1ad3d1be4398ecd90512801ad895b0ea; original global index 8169.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 69c1c2d6c661bfdd000d48a71b8a7b8bd1de4eead499fca20d17c84d9194031e; original global index 8231.
def localCycle00112 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 6a57f3fdfa27af23a704dcf7b63dc1d9af1693e49fc705caaf7859f6a6a984e3; original global index 8280.
def localCycle00113 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle 6b32051ba2dafa04cd018ea1bf84e57e221c3081a70521bd589ac142bb7ea5af; original global index 8343.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 27 1, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 6b7e03347023190e86fb775b445582f69f252dc26d8c49d81b64798a4c8d5762; original global index 8366.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle 6ba7db2f79bbab6d76ffb5c9c2e1d381cb4e114bb2b1e0df1102ed076ddcd112; original global index 8378.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 6e1c16e0b2dd64e03cefe200615b709e23d595a1dde6ee10952c402f56d32de0; original global index 8549.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6e5b4dee820daef98c6a9e6d12334616709d05e14b59ecf29e06a1f4724fdf42; original global index 8565.
def localCycle00118 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6e700030893f7c6db3d7397b3be4bec96185911c0143a992c9b83f3b7748b201; original global index 8570.
def localCycle00119 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 21 1]

-- Original cycle 6f6d5797313ae9a758f9ae79c21d9e8679c38b545a5ae1ec550e9200fad903fc; original global index 8640.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7010745a0ee67b9a3cc50bc0ac248719a427cb868e69f8c52e1515e9f27195a5; original global index 8687.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 23 1, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 72e5526225509a8fe14170334f0ef3ec4c1462c4ef3471f4b0e69ff2fb87f23c; original global index 8903.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 15 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 73eb32160626058c0ad777cfd2177d936ea41a7f50f62ec93fd28dfd96c51ec9; original global index 8990.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 1, .gapLower 6 3, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 7536d3d71df16bc843111da1f305a143ac83519db4636fdc70b8b580198e3f72; original global index 9082.
def localCycle00124 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle 76e4136af6a8b3da1b74a6e952566b7245af0d64a809ec762034462225f8139e; original global index 9202.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 4, .triangle 15 1, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 7921a8146dd65ad8ff2206f434ac65066c3dcc1cc49d409fb1de2903366b61a2; original global index 9373.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 79caabbc8e80b48249883cbeb1f6a49e4dccb97b304b500a0279e50ff5358f12; original global index 9420.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 7d1d5accab54862ee06dcd9bba4ea7e47e4635f4537fe494487d4ddb2f4aa56b; original global index 9691.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 7d804511bcda1762bb4841af705559e5aa7ecd0faed2c8b9ecde3a4613e32f20; original global index 9738.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7dec1b5d3bcc9c624a788025774b42b6153fb972e5dc125e13e12d40e1f51399; original global index 9778.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 82126c5cb9c27aac91d9af65a58226a039556dbb65df050b00b55ae78c26df30; original global index 10099.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 18 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 858d8d74c99e92c6f42c9079d9fc951f16694930facced220ec5fc9c4e1eb65e; original global index 10364.
def localCycle00132 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 87729843a08619fc416c4c16d5da5973094422c2983e1779a2ef0e2ce6b942e3; original global index 10505.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8ab1e75b33a745b07e2ad1e3defe2934c019bf71f59d0b20332587d11c5682b4; original global index 10745.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 8b2b05719ebdcc8d2bd2a95d290369cfb0d424e629fad729d6e0c6f4cea1c3dd; original global index 10781.
def localCycle00135 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 21 1]

-- Original cycle 8dafe81d24aa4b058238605e25123861851a1185416b1dd7d89cdb9ace227121; original global index 10960.
def localCycle00136 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8ec210d9460cf03edafed2190b02916c24b3eed999f9b4c06698229c7d884b8e; original global index 11048.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 8f40306db476870f7cc76e0fd64eedaf6690443ddb67624595322a10705040c4; original global index 11085.
def localCycle00138 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 0 4, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .gapLower 4 0]

-- Original cycle 8f45ec0d1c53fd782898fa064f1c6ef5d4a2584ba8c62c5418811364345ab350; original global index 11088.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 90c6327afb495a7307809647ebacad158d4abc79bd1c980edc757c54e03dad4d; original global index 11210.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 27 2, .gapLower 6 3, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 9126b6d7e2ccdb7f66223690845eab18748c4f42203cebd518fe4d23f33b85d4; original global index 11241.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 957c03792a88374e0ccbd026d9834d3d93c0aa29dcbaab528aa77896d5b69976; original global index 11618.
def localCycle00142 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 965d8deffbc6b01599cdc76f1a5cdc86612503589302fc7d62906e8058bff48d; original global index 11690.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 1, .triangle 27 1, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 971256ac27eb819a4932fb65d92f5e2946cf8db759899bc3fccabb6797056e25; original global index 11741.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 977ee1d5b7b1074e95d6828dd1e5700472067864b3ddff730b3af7ebb1ab96bf; original global index 11771.
def localCycle00145 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle 989cc21103447b2699bb24b0c33207fb760f473be110e912e6189e292eb93f1d; original global index 11852.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 995fd66b5ac5a9d341ecd8b9525e6b9cbb1c3597cf65cd37d8c7c9b662a8d0be; original global index 11909.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 99ce97ca50620f3712e609f8e136741e0302aeec20fd8dfcdc4384a7e54ead49; original global index 11940.
def localCycle00148 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 9b56369b16bf76bf8f617743d9d6a8080766e80de09a20516d07e3845c00f2d0; original global index 12081.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 9c372e8a85c9b74def3e165b0ce18d90668678b2f568362218f2e5117aa77335; original global index 12154.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle 9c8bbdc66beddecc0ca539277646e553f2dfca07652e8b61e1859d169262b9df; original global index 12176.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 9cb1a82636a42511b43a8b2d3c8623adc81f612777e09e324b105c6861fd0169; original global index 12188.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9cbd7dc368c890bf078a59d089c50f57a4413e34e3f0dfcf101873e5a2a7ea7a; original global index 12192.
def localCycle00153 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 0, .gapLower 1 2]

-- Original cycle 9d4b8f5c3e8eb1b655202cd98457e97fe0c826e2852bc7e4965ab43454986471; original global index 12236.
def localCycle00154 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 29 1]

-- Original cycle 9eed31e041ef471f27756e91089636f3e05f2ed1e4a88916c5c07062043f1390; original global index 12376.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9fbfad4a6ca5b5357d8f6b0bb235eb21b63b6b477368539da885c6a62fa8a85c; original global index 12433.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a0e6336b6a84dc7956c8abda25756495bacffbd5a7a81938672cc1e6a896e776; original global index 12515.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a1a5855f7b4dd5d6136f4d4a75db14ed37a16539627aaacd6b6f8e4ef61630c1; original global index 12574.
def localCycle00158 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle a20f9d1d7d6268b10d7d77ad6126058a7b12d39a42285981c3c1fce2d874fb8a; original global index 12605.
def localCycle00159 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 2]

-- Original cycle a3687eff937b1f74597cc69c617738e9811dd62c1fefb1af6f455194bc9438c2; original global index 12702.
def localCycle00160 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 19 1, .triangle 25 0, .triangle 5 0, .triangle 0 1]

-- Original cycle a566e735e68868e8d72eae1b02a14c6a72e760778e07b2da2c77c1b8465803ee; original global index 12849.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle a598f13d141e4b9d25b8f1316ad5269ccd6e57c4540a8809bdbb8f4e217a0cb6; original global index 12864.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 23 1, .triangle 29 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle a5bb7b5c7d4e2e4760a681d086ccd59e48d7afa41554849c880288a70ead337d; original global index 12875.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle a67a4a85504edbda0cd2c9dd39b3e10240f88bd5114aaa767b9f6b11d3f0e4cf; original global index 12931.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle a70b1d8bfc2c67d65cbc3366aac4f4b3f9d7237051b0e4ab9206fe71ba593481; original global index 12983.
def localCycle00165 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle a84d57edc1a5378fb2903032d13805ee6ee360ab3881a3eee3de324314b4987c; original global index 13102.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle aa8e1ab38e50b93fd8a7257890539a81e589eba6d4bde628e7aeed9317e47181; original global index 13284.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ab3582250043336750c327a125b744806d6abeb0585f7025960b8fdd2ef21b44; original global index 13338.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle ad2fd697cd0894e9916c59b54cbfcba03f551322603698d260aac0a2625590e1; original global index 13500.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b09020f46f3ec4fa483df5d4f219a88989328ec7fe31ac6a63c683cb96397dac; original global index 13785.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b0c0da8f8485d5c2912f311e098502a9142bf2607af406e4135679aa6b9ddd41; original global index 13802.
def localCycle00171 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b33813335857937071f67fe67a59c1290574298a9855f3071a7130600a5f8a70; original global index 14007.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle b52e3c283c578047ee92c60ad4c8fae9ae1313bd01a64d080774267d50f75b57; original global index 14157.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 4 6, .distance 2 6, .theta 2]
    constant := ![3, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle b7ad8b5ae9a25f5778792196d06df86b5556ded377aadca5e91a70a156769659; original global index 14330.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Original cycle b91d5127030eda7debe210455082766a97cd2ea79252468533684445a5befe19; original global index 14445.
def localCycle00175 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b94fb0559ebd2dd2857f868638b86bd1bf48d906321ab055725a6c34ef98c9eb; original global index 14459.
def localCycle00176 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 4, .gapUpper 2 3]

-- Original cycle b98ce9d1f8423b7b6cf213d56354cba88e6dc60bec39e415b880a57105e2a561; original global index 14477.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bcea57910618885f18b1aadb759fc6c097c7fa1449180ad588775b37f0429745; original global index 14738.
def localCycle00178 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bcf22c71a3cc25996a49362a77b423a89c70f5894d4a88e15264ff4153728ef8; original global index 14740.
def localCycle00179 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -2, 0, 3, 0, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 23 1, .triangle 29 0, .gapLower 2 2, .corridorLower 2 3]

-- Original cycle bde254f910100be3cd97220f616bd1ef681b88e2f16e55a1308ba811c7a8d6d6; original global index 14809.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle be778862b44d8b25f369eb3124860de0583ec45632d7e07b246754205417b6d4; original global index 14859.
def localCycle00181 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle bf5bae3ce3b3ea74e47afbffe35960d51396c5e50a604ab2e0c4c2680152a187; original global index 14933.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle bfe4153a8741276c4cb8cf7d0cf2a95aacbdae2122c46e70c32c10921be9785f; original global index 14971.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 27 2, .gapLower 6 3, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle c009110a5d749852d8f34671008d13f54d5887ee0786b16c52504fea8aeaa39b; original global index 14989.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c081735dfdfeab0b506ddfc985470aebef06270f1525cbb83d3857c04a8428b4; original global index 15028.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c0e8db71bf705a4a9dcf8fcdf9c2a9f28c89f066c752edee22c2b3c51db02953; original global index 15061.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle c149e9c9987dd872cd8bb26d7d775567f41c6f566f16ccef2b549e5544e4bfed; original global index 15092.
def localCycle00187 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c19321dbb69666de97c4d31e4162c91599c6f61ad1f047e5cfb007f69a70737b; original global index 15119.
def localCycle00188 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00189 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c47ed88aa0a9a6ce598bb3a57e003652ded070793fd57d1f3c98801df5c6b065; original global index 15322.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c4ea6ed3886cf530a65a4afb2ce9a4a092bc765866f2b0669c5df49322c16c56; original global index 15364.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle c52e7436dbe7b66e1f12ba69130b7fdbd29c0ca6142e1a72cbeafd901172cddf; original global index 15383.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c5dd077482b0a5da3f87d6856ff87d869c52b40c9b4eaae3e6092036bc0aff62; original global index 15428.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c737149c26708eb3e48ab5824a0349f7e2f8ffd5c7cae47fef669d03da2010ec; original global index 15543.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c781294450e83b072d240a77a9d433680bcf3a881cee33ca1416404627715815; original global index 15570.
def localCycle00195 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle c7bea6383c06505686eda937657e44ad2c615f35ab25c5a9391a3415b1b35447; original global index 15594.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c87e313d19505b6fe7d36083a6bfaaa113a8efd9693a5fa1aa551bb3f9455aaf; original global index 15658.
def localCycle00197 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![4, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle c8a1b45ea6ac488f41d777c75a3499c5740f8fac26935920e672452bbe546e87; original global index 15671.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle c91386e8a6302e1e1e06c1e720ebd8ba02a9f92c44a3046b18407dc70c34e444; original global index 15706.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 23 1, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 1 1]

-- Original cycle c998b3e6424f71ad41faf31dd4ccd509cb490f912279083d9ce4f47eed9dbe6c; original global index 15762.
def localCycle00200 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle ca6d0549a9e8720e6e9de3ccf1ee96a9dc3aeee1b375609da4f638142bd83d61; original global index 15823.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle cbce652eff558eeb6f835878b08a0db813f68635681821be77fc047d9c928abf; original global index 15925.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cde6b2909bf10f9899d87d3753cb71994908f84cacd74b7dd3414466b0b2202b; original global index 16080.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle ce56a8d45e958b1cee469d43183fec6c216ca0d73694b6b60ace813577c86258; original global index 16120.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ce884f9e7e891830b6003c539e8470f37d13ae3dddb8f5150911db13665354cb; original global index 16129.
def localCycle00205 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle cf4b14911eeae35b4e9de83fcbf7bd97a08a50c22c9252cff53e233a474b6c5a; original global index 16178.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cfca60c671ea94a15279faf614c96528ef908b1f16035a94696870f70bb196bf; original global index 16215.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d057ba840b77f349e4aa366edbf8803b5eef688feb9932e7a0a89969ccec9dd2; original global index 16261.
def localCycle00208 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle d070ca4a6b3b3b1ae91cb82775643b65547bac97f48f070bcddd910956852a9c; original global index 16271.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle d0be8c393274c946084541dcd83818cc576851217134d0657d942148df777b12; original global index 16291.
def localCycle00210 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle d10b5e974155c4b5b17c83c58c87654042e18568792212af6e4a691ad1376fad; original global index 16323.
def localCycle00211 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .gapLower 6 3, .corridorLower 3 6]

-- Original cycle d1e3ab5e70d293eac61af6b7c0a8370af9c81cd24f1fc7d0e1cf98a99c2380b3; original global index 16381.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d1f9a7ea6dc4672df44fb747e65cad456bf94d8105abcbc02e3ecc02d396dd65; original global index 16387.
def localCycle00213 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Original cycle d2488286b202ac351137987d12717c91ae06e41127aeafe50385e5687d4b1439; original global index 16404.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d2701863c44e989d1b0afd09e8985d38c2fc23188b3fa728dc1625ee60190e80; original global index 16422.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle d353bbbafd58cad2746f6e4b369b3b1b2b7e81c5a31749d7308963fc7fc7175e; original global index 16484.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle d3a783478eab03865e1b39122748ba7c9a64d6e0a6d4aa11695d526e74c73e6c; original global index 16514.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d3fd0b6063cb6d2e3440fbe77ecf323aada2160b879104a3652945317df57e17; original global index 16544.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d524de5e32394d746aa7de362a84ae7812123b509a09e845bc02a2c559ee2280; original global index 16630.
def localCycle00219 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle d9366ccd444008b33fb973bbfb3f93b4727ee7c4361cd3213930408fd2717ab4; original global index 16971.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle d9b87e0de290f3c29a84e23212c76e14860381c25bcf7c79d17df66cc1e38f49; original global index 17007.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle da4eb1a816a92288d2af1e286e981f08f79b288b7884b8737423fa84b2c0d8a5; original global index 17055.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle da6d3a330a87f035eac15e0d7fa0b65980703609567e7e436d74a87f68494aaf; original global index 17070.
def localCycle00223 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle daf618e7090458a96c1d4b6b1a600a0be39fb50f5bfee59cb5cd61dcfce9920c; original global index 17108.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle dafa7a0d1453d755769c7418443c4f59510d5369a3ef5701f819b27952b96aa9; original global index 17112.
def localCycle00225 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 0, .gapLower 1 2]

-- Original cycle dbe5bf2cf39d2a7eb5163da13f79f213d28f3d8622f0ca7a98a6a14b637389fa; original global index 17186.
def localCycle00226 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle dd42e1d043e7c2cae3073b25e1772212eeb90c84c5b9c432c0553587204f7a5a; original global index 17300.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 23 1, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e15fcdba8f9dea3ee4a3f10e92cb5f77d08443a5dde5db65a850bccb0a86dd58; original global index 17625.
def localCycle00228 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 3, .gapUpper 4 2]

-- Original cycle e232e27e17761e7b70ffc472cf0d889cf6be9b257651eabbfe7f30a1e5f9f5ba; original global index 17685.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e255c3f729f30bc036fda3190796893eb62e33f9cf7ae14a3bc98ab28c8e3ed4; original global index 17698.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e2870a422347a35974b54c5fb268eb7fd0d175406879792fb61fb841c1eb77eb; original global index 17714.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 21 2, .gapLower 6 4, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e324206b9f315a43fce9e469fa76d290eaa3ea7a5b31714899b7aace841502fe; original global index 17767.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 27 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle e3bd208d5f640977fcc9c23d9d422dff53288e8dfed9eeab7e68fda16757385a; original global index 17813.
def localCycle00233 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e3be1e4367636b83f92133ee7b04511d7eb165d6cbb392750a43629a50274b66; original global index 17816.
def localCycle00234 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e4c0bd6d5b9944d014c04150f7c77c80517084dfaca7029062f1c78479dd53ca; original global index 17880.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e554c934539ad50aafaa8a5b435b3b538938f0e4f8da244f413ded3917874832; original global index 17930.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle e5fdd7d37a31cb7ccd05eb620b974881cf9736ff0fbe11af2e0c522efefafe53; original global index 17999.
def localCycle00237 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e66d6ab94e1b963f4ae5dcb4b4e79d933862f6faf980020cceec79d4d1473a8a; original global index 18027.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 0, .gapLower 6 3, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e7950707f58d55ce80cf30e6a8cdeca80c643a39a80c153773c19193958d8dcd; original global index 18110.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e7d4a0d02c4cfa2b5f57c09b70513ceac383b53dc4a816f2f0834d5073896146; original global index 18129.
def localCycle00240 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle ea0a1d278e4a3911822dc642f53ddbfdf8a19c8e11e78f829dc751f856f39545; original global index 18284.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 0 4, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .gapLower 6 2, .triangle 13 1, .gapLower 4 0]

-- Original cycle ea557ea6c1d5ea2b7c27d25c8648d4bb2dd9d58f324873d2cd4d31de93586a0c; original global index 18302.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle ea850ff622e0a5390996dd5688f50d6aa6956e50c940ae2f76e2978f643d8f44; original global index 18319.
def localCycle00243 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle ebf0e3733e4d616b2a1ee5250747acc36c6dce11f6b0024801fcc56d9de896a7; original global index 18415.
def localCycle00244 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle ee22b45e5732af14660abe133ddec3116e899aa4aa8c8ef4984f6b95e7fd4641; original global index 18587.
def localCycle00245 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ee9cfed25cd31422b638e569729dfaeb81d4df1c220328d54dc56b7dcfe621f1; original global index 18621.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle eea955bfab500389ca584ec34d3434900ba033be915bcd53446d15be68df80b1; original global index 18626.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle f002850e4790ea8e86f8e1747178d8a9c8523062804652aa588857382d6ecbdc; original global index 18726.
def localCycle00248 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f062ac5595ca988314022cf38da57eea69bfb6fb34c90e2767550cb0735a2aa5; original global index 18744.
def localCycle00249 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f1014e3fe9555811dd96b49c907f901b4beb3885e6eec300dae1f333bd13586c; original global index 18798.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 1, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f113fa158cf54ff589f0d4c5a992fd0c385871c104b7690a2277cd884b49edf1; original global index 18805.
def localCycle00251 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle f2160a6053cf0eeedc07277706dcc2ccd71e28e0cfa219edd786ea3fb6dc2079; original global index 18880.
def localCycle00252 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle f3c80eb2234db57779a8231ae1644a30d88d620dc1650ba06c9a0063c84f29c3; original global index 19017.
def localCycle00253 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle f46ce9b54a78c0df8b61ce753a4b635a0a77043c0036bfd76391abb33ecc3e10; original global index 19057.
def localCycle00254 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle f4e5cfb4de382d31425da39c829c3cc332ad772cea4f1dff9e039bbcc4e19330; original global index 19094.
def localCycle00255 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 29 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f70225bdb672e6781ec0f73c51cbecd6d7afe68189da96b7f862bc64396f9f53; original global index 19265.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle f9f75713f6531ded1525f28ef8399dee57f1869ea9b7a8d43f3891ddc013fd3d; original global index 19490.
def localCycle00257 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 6, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .gapLower 6 2, .triangle 11 1, .gapLower 3 0]

-- Original cycle fac992919ad99a9b847d27297bf591aa070f9ae4748f229432dd456ab1ea64cd; original global index 19566.
def localCycle00258 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle fbe8d841c7a54003c46ca9813673b0082006c0751267c332e9574582bd6a5207; original global index 19665.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle fd404bebfa65f8cb6b2eb64e9a649e66c8fa6c3fa5e2cf1c748f889a3e4c0260; original global index 19792.
def localCycle00260 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle fdc3dd49470ede8af8b654cabb0de725c88a36c547951e1c86f2a9c8be316c77; original global index 19833.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 1, .triangle 29 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle fea000a3caffa86cad0a868617505754712428ec107133dd2b1dacacc036e926; original global index 19907.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fefbeebcd8f5567aad3eada37d4656bb19c997c02fd3223529f0a11ec0e371ae; original global index 19936.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

def library : Library := fun id => if id < 132 then (if id < 66 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 49 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))))) else (if id < 57 then (if id < 53 then (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 61 then (if id < 59 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none)) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))))))) else (if id < 99 then (if id < 82 then (if id < 74 then (if id < 70 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))) else (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))))) else (if id < 90 then (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))) else (if id < 94 then (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))))))) else (if id < 115 then (if id < 107 then (if id < 103 then (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))) else (if id < 105 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 111 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))))) else (if id < 123 then (if id < 119 then (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 121 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 127 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))))))))) else (if id < 198 then (if id < 165 then (if id < 148 then (if id < 140 then (if id < 136 then (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 144 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))) else (if id < 156 then (if id < 152 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)))) else (if id < 160 then (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none))) else (if id < 162 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))))) else (if id < 181 then (if id < 173 then (if id < 169 then (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)))) else (if id < 177 then (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none))))) else (if id < 189 then (if id < 185 then (if id < 183 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)))) else (if id < 193 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))))))) else (if id < 231 then (if id < 214 then (if id < 206 then (if id < 202 then (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))) else (if id < 210 then (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))))) else (if id < 222 then (if id < 218 then (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none))) else (if id < 220 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))) else (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))))) else (if id < 247 then (if id < 239 then (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)))) else (if id < 243 then (if id < 241 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none))) else (if id < 245 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none))))) else (if id < 255 then (if id < 251 then (if id < 249 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))) else (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)))) else (if id < 259 then (if id < 257 then (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id = 256 then some localCycle00256 else none)) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none))) else (if id < 261 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 187 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1024)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 105 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1025)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 182 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1026)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 144 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1027)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 204 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1028)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 4, 5, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 34 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1029)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 29 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1030)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 78 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1031)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 5 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1032)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 203 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1033)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 125 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1034)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 4, 2, 1]], proof := .tail 219 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1035)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 150 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1036)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 6, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 73 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1037)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 142 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1038)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 172 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1039)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 167 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1040)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 151 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1041)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 3, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 178 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1042)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 63 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1043)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 6, 1, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 39 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1044)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 6, 1, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 240 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1045)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 79 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1046)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 39 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1047)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 4, 3, 1]], proof := .tail 260 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1048)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 127 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1049)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 6, 4, 1, 5], ![0, 2, 6, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 48 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1050)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 83 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1051)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 39 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1052)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 6, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 115 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1053)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 6, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 26 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1054)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 141 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1055)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 132 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1056)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![0, 6, 3, 1, 4, 5], ![0, 6, 2, 1, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 52 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1057)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![0, 6, 3, 1, 4, 5], ![0, 6, 2, 1, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 205 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1058)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 71 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1059)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 147 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1060)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 175 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1061)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 215 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1062)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 3, 4, 1, 5], ![0, 6, 2, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 87 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1063)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![0, 4, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 42 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1064)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![0, 6, 4, 2, 1, 5], ![0, 6, 3, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 196 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1065)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 149 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1066)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 29 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1067)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 0 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1068)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 1, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 2, 1, 4]], proof := .low6 (![239, 61, 257, 113, 176, 189, 60, 157, 193, 238, 229, 99, 99, 58, 197, 27, 10, 201, 180, 18, 58, 58, 72, 211, 211, 244, 131, 136]) }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1069)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 6, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 223 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1070)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 142 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1071)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 242 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1072)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 4, 2, 1]], proof := .tail 168 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1073)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 16 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1074)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 70 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1075)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 47 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1076)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 3, 4, 2, 1]], proof := .tail 29 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1077)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 200 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1078)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 2, 1]], proof := .tail 96 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1079)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .low6 (![86, 195, 20, 67, 262, 17, 234, 191, 38, 93, 12, 54, 129, 209, 55, 134, 245, 122, 198, 25, 158, 122, 249, 106, 6, 212, 1, 248]) }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1080)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 185 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1081)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .low6 (![86, 45, 155, 74, 37, 153, 46, 56, 11, 186, 19, 225, 95, 230, 170, 3, 225, 107, 138, 207, 225, 190, 254, 225, 255, 208, 192, 225]) }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1082)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 3, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 263 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1083)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .low6 (![86, 195, 20, 62, 119, 213, 57, 191, 38, 93, 12, 124, 14, 209, 55, 134, 124, 101, 198, 25, 124, 101, 216, 124, 114, 188, 143, 124]) }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1084)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 233 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1085)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 40 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1086)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 4, 2, 1, 3]], proof := .low6 (![64, 164, 76, 159, 80, 135, 75, 177, 49, 23, 152, 250, 43, 258, 110, 22, 53, 69, 148, 30, 261, 112, 103, 123, 228, 59, 231, 146]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1087)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 6, 2, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 41 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1088)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 137 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1089)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 5, 4, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 2, 4, 1, 3]], proof := .low6 (![86, 92, 241, 154, 174, 135, 36, 243, 166, 139, 133, 179, 217, 156, 130, 214, 117, 31, 108, 126, 162, 104, 50, 121, 173, 100, 88, 227]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1090)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 6, 2, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 9 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1091)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 2, 1, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 33 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1092)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 3, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 235 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1093)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 63 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1094)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 39 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1095)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 2, 4, 3, 1]], proof := .tail 202 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1096)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 206 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1097)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 4, 1, 5], ![0, 2, 6, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 66 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1098)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 83 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1099)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 39 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1100)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 2 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1101)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 120 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1102)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 163 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1103)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 4, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 2, 4, 3, 1]], proof := .tail 202 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1104)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 6, 2, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 91 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1105)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![0, 6, 5, 2, 1, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 260 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1106)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .low6 (![51, 44, 35, 140, 247, 189, 60, 222, 184, 98, 68, 169, 169, 171, 82, 194, 10, 218, 8, 232, 128, 128, 13, 65, 183, 244, 102, 136]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1107)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 7 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1108)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 97 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1109)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![6, 0, 2, 1, 4, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 4 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1110)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 87 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1111)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![0, 4, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 259 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1112)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 1, 5], ![0, 6, 3, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 237 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1113)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 251 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1114)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 5, 4], ![0, 6, 2, 5, 1, 3], ![6, 0, 2, 4, 1, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 9 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1115)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![0, 6, 5, 2, 1, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 33 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1116)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 1, 6, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 81 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1117)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 6, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 181 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1118)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 89 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1119)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 210 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1120)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 3, 2, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 109 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1121)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 3, 2, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 236 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1122)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 77 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1123)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 220 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1124)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![6, 0, 4, 3, 2, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 224 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1125)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 2, 4, 1]], proof := .tail 226 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1126)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 161 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1127)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 116 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1128)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 15 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1129)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 252 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1130)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 2, 1], ![6, 0, 4, 3, 2, 1], ![5, 0, 4, 3, 2, 1]], proof := .tail 221 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1131)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 5, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 160 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1132)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 118 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1133)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 206 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1134)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 2, 6, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 84 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1135)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 6, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 21 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1136)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 94 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1137)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 165 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1138)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 3, 4, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 165 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1139)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 5, 1, 4], ![0, 6, 2, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 32 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1140)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![0, 6, 5, 2, 1, 3], ![6, 0, 4, 2, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 165 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1141)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 5, 1], ![0, 2, 3, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 24 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1142)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 2, 6, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 28 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1143)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 5, 4, 1], ![0, 2, 6, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 90 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1144)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 5, 1], ![0, 3, 2, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 199 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1145)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 4, 5, 1], ![0, 6, 2, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 145 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1146)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 5, 4, 1], ![0, 6, 2, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 256 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1147)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![0, 6, 5, 2, 3, 1], ![6, 0, 4, 2, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 246 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1148)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 2, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 253 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1149)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 5, 1], ![0, 6, 2, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 111 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1150)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 5, 1], ![0, 3, 2, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 85 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1151)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1024 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1024 ≤ id.val) (hhigh : id.val < 1152) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1024)) = true := by
  let j : Fin 128 := ⟨id.val - 1024, by omega⟩
  have hsum : 1024 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1024 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard008
