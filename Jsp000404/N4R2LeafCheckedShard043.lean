import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard043
open N4R2RowDataReplay

-- Original cycle 05a10cb9545bc9061708b748ba73283b81f412dfe9e132820d1745c1275eab1e; original global index 466.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 08c9bc4414bbaa56d64827e51356b1c1825d0fd0cc08708a784102097b747dae; original global index 706.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 09778e4fca5d5fd500bf01d80eae28eb5dc4baf34c62a3384c7faa07b94859a6; original global index 752.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 0fc16b3e1ffbabdcdd89a3cbc3361dedcf4c61d362f0c00c82e4ec176d2ef73b; original global index 1256.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 152f0f1b3f920b04a2453b95d507ddb8b7d5edc4644c6b0b9ea71e3ea63bf1ff; original global index 1677.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 1a3727c8d367a0f0147226948c762e488b69b2a5b5ae84fca9cade7662d6ea0f; original global index 2048.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .gapLower 4 3, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle 1cdeb86fa29dcfdfbac520cf68d2a772214e1b3ea04f8a461b24b0a0ba14dd09; original global index 2221.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 1d240861f9f248b361424b400511abb0039e048abe2a8c9804c70bc0dac3f19c; original global index 2245.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 1db8065408b4f5c07561e512cd35ca2ac537e4047468dce5c9b8fa6f27466b25; original global index 2285.
def localCycle00008 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 1ed9b5089426b83901c48d4fbc29913e2d8a210e0263d80f1b213d0ef168a3bc; original global index 2369.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 229d0f8f2fd3577efe3ba40e74bae8f5d8ce00acb3c37cbe66e81963747dc5bb; original global index 2647.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 271f0397601996982c4d25491800f77c58797905d03ad9909bf49b4503a2cd68; original global index 2997.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 5]

-- Original cycle 28bcae61e86bb653c559f098c18e6d5a5b1b3b103782709db3508793842bba67; original global index 3117.
def localCycle00012 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2d2d9fa6b5054aa01c3bc0f30f0bd9c34204623e75ce0bfc8c6b46d564b6d345; original global index 3447.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 2dce5619a65aa98f0dd0ddd18ed1d461548124c0ea04aa2050afc183102b6a28; original global index 3496.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 2eed69d6991fddb8c9e6d829183aea191d1b3a55a901e07d91eecf3df201e5bd; original global index 3591.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 31c814848842c38ad230d209db75195b9ba49d8dac194e1dc55bb5952d90509c; original global index 3802.
def localCycle00016 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 325258b36ad97d4321edf478e15c7dfab4f6f2904266474fed440c8b61719e4e; original global index 3845.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 34fb34db3440e3c66685bdc52fe47e3cfe7482b064a1f868db958572082cbbb1; original global index 4054.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 358bfbf943b806032341e1054aa0cfcf1f27ba6af43e7ee28f2821110bc1d872; original global index 4101.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 396683c22c9ee37f0775605fe4be2fa90b45cf49fe9d2fd80d0ad4fbf3e2109f; original global index 4421.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 3c145cf7f7a23eec587599e3e9cbb95416febbd0fed9793f7057cdaa862b9a5c; original global index 4656.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3de3201d7ffd38b12b4ab6a69e2c2d7c89c9f18d99114c9871fd30aded1269b5; original global index 4787.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .corridorLower 2 3]

-- Original cycle 41bff1dd335ac1b97ea482487d2cd429538c90d27fef4b84eb187cb0a4af3973; original global index 5070.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 460b2f8d3e4b44e7884c70f5c4bf3eb55800e64555836f84c54c90385aa82081; original global index 5420.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 47ad5dd5f48dd16f53f3e79eda9f9904e1f0be44496ad097e117869f5e6fb707; original global index 5549.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 4b1277d89190984edea1a5626d2c314bd7745f4776596e32a084818f5516bb40; original global index 5826.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 4f353aed653924acde5b44b7f79393e897ccae0d65496ff6485e97fc447aabe8; original global index 6157.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 32 0, .triangle 29 2, .triangle 30 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle 4f8e098672202c918cc55c07f8a2208b5972de0f9243487dc3aa6864aa6de48a; original global index 6179.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 31 0, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 500e918d2777721da7414b2f50ca59106ae992e333404ed0d7068c72c190ae7b; original global index 6214.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 503b87e0754e07047a5dc6ece2e4bb00368ac22d127a07e28df97fb55b87614d; original global index 6228.
def localCycle00030 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 515288dad2f2412fe0a11e2377d2c09e96d6a6f78f6272310582ea903a7c5a57; original global index 6321.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 52d743c18b520077c3a399964cd3f18c31f29483a38b852bd93b426945ff6d53; original global index 6451.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle 5533750f3458e5c847d0ea1c936c4984e20e83370994b7143421c70dfdd30921; original global index 6596.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 5a00cb13076253e719b9fbe475b4238c83053057b74ac9eb70690361269397d0; original global index 7007.
def localCycle00034 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5e61cb079ef0ccf857c0f0af5b7f81f9f2cbdb27fc4b617731286bb9bf001746; original global index 7343.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5ee105caacb348c0712278b565d6825dee5c6962ddac1a3027db1d844c190765; original global index 7384.
def localCycle00036 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 61ec83b1ac77f02b845c207ec60d163718306f536b442d6e0f01b2c674f1d12c; original global index 7645.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 671ece6f18c240e03d89d755888fc861b141804e2e018bbd1df0248e5561faaf; original global index 8017.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 68447a2bfc4f2a3db3ff445d777331431040f0f06aa5b8762c32395cabf898fb; original global index 8111.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 68b14b9a33ac0fc1a1125ea0d515a0e86b49353a7e78076e2ead321d11fb7a79; original global index 8143.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .gapLower 5 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 73136d601c5d4abaf9f458444c497f9e2e3d084c25ee8ad7319431dce541707d; original global index 8913.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 74030ec0ef2e5684ac741d4a5f1ced41f7043ea37ea981ed7cf08aef0ddba0cd; original global index 9000.
def localCycle00042 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7832431ac3e552b5cb7d9b50acb9ea582f11066905bb13c295381a9119409e2a; original global index 9288.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 78565d8f2d4749823cb72db3ab526c66f7487cdc5a4f9189b50d84eb412e3604; original global index 9302.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7cefaca7b6ea88cb2f4e4c90d54bafccbe405fe4f566aaa6158a14535192a198; original global index 9674.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7cf406f6ff441e3075d96664c9abe72b276e1021ad514254581a058e097335b3; original global index 9675.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7d683e85e931f85fef2c08ea77a4cb6fe3d2be6c01d55e12ff7a9531fd889326; original global index 9721.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 82316841a8b0a0342446961da3f75e44c20dfb8e3652d00645b81b5d478347ed; original global index 10110.
def localCycle00048 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 8268d0bc3de0d3a9521a80463a380b578dd0a47627c1ceee2e125c8a41f49864; original global index 10121.
def localCycle00049 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 82c5506aacd9855be3d83c522f18790997bbe2280657c619ee73111085acdf06; original global index 10144.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 86398e04879dd5ab6eddf55d9a38cd6ca72bd80f1e3b6417f17edcf401e286db; original global index 10408.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 880c2831b9ae01984a0bedae3d234283d878950354f5d368aae2d3f6a847420c; original global index 10550.
def localCycle00052 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 8f67f13a922b35c73352bc0e3ad0aa855867f7cf0e47c392e7cadec67a06278d; original global index 11096.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 5]

-- Original cycle 91c322a36cb7e7d595f226bf13888c3123fa5b4d51c5990e6ba70e9483634e7b; original global index 11297.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 950ad450a51cdbda6a2d49f103b93a779e370c451a71e4b6c63487387fab93ec; original global index 11574.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 974f1ebeda31fc5d80bf5b1c9a84b2c6e1b70962e2a16f8f1cf9e97dd1000237; original global index 11758.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 97e9f54a8c397a4f8b5cad9b4395e084654e1bf76d45d74e53b33a8ec5509f2b; original global index 11797.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9a3c7b0592537317a98c76964378270096d72009cdf7cb4bbdd592bb073ef13c; original global index 11984.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 9b6e20c0c91d1b4af39d76dd2b9234ccd0511d06a2f0b805e035cf91d25fe85f; original global index 12089.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle 9dbb5180725e0d218750825b3c537f7ea8746bd4b930a385abfbd499c959ea0c; original global index 12273.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9f908a41847e16709b2966ae2aefa84181a7077f791c9d81d3a175a89924b420; original global index 12418.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a4652ca25d60cf019f7d39157489373174e8d79ec97a733cb454be38590c3fd3; original global index 12778.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle a78d2e29e347865295bf61652ddd48611b0e46b24d7762d44edcc32cc94d13f5; original global index 13038.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle a7d6cce89bd2a06bf17fb8143563a301060c3cb439f6b95fbdfce5a78c953351; original global index 13063.
def localCycle00064 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle a94662074f45c961705b862ba92d4c8121511d9daaf90a0871ff05d0b57a036f; original global index 13181.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle aca15d6a6085eeb815062fe7e840a047df785eca76d3fbfa8fc7ccaae679f1dd; original global index 13457.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle ae2ce4191aed9c0eb6d39f5e50be5af0e2aa936b5281a235338fb807eb6a2ad1; original global index 13594.
def localCycle00067 : Cycle where
  length := 15
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle b237e967e4210ac44060c47b9bda58305168ae1225d7e8662f6417471794801f; original global index 13926.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle b33c59d0e498cb59ab06e8b82bf666c565ecde8833528bbc63adeb2c024f0dfd; original global index 14009.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle b3b4d40babb63135b097b4aa7bd3b086b36d5e2ea57ec30cdd3bf0fafff235dc; original global index 14036.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b45479689e23feee5882f0cd949e17ae3928104316c843d77ce65fef57b64d6b; original global index 14086.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle b48cf1ccbbd870ac6f37caaecade174324f28f6816408dd4c9dd50081d32833d; original global index 14101.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle b5ddc4b1460858a2c59193e191eeec2d725cb6a94f1965a72a280bd6105cda5d; original global index 14209.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle b6477bd340b4a0e6d9a28291f49c643ee6552975e2a68d9bfe63a916eadbccc6; original global index 14244.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bbccfec36b602dcd054189ca100e66b1b5d7e68aba66f2d780764f049af62f3e; original global index 14668.
def localCycle00075 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c081931b4e86f00f2ccd9caf8c8cbbd05ac94a98907c458eec969e6935760d58; original global index 15029.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .gapLower 3 0]

-- Original cycle c142bd0e8913dd075b40f2737d5ebd158fd9954a6e8f5bc55f8be58bbe01cca2; original global index 15087.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle c303fbbcd4d7bc658db6951c8e3fd29a0ae15d80dfe6f63f3b02693e5555835a; original global index 15222.
def localCycle00078 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c6fc203cbf2e0c7b70b80a781075c3e18574ea760d3ec5e2eeb2546627691c1d; original global index 15527.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c7697007a5d201db61c2623e8a75f7cf572237c310d26aae6da4b9d0d2e44510; original global index 15562.
def localCycle00080 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle c8a6d60457e929a36e757f1e7bb3cc5c4c4a21c68aa0ff4736fdc46f6f74399a; original global index 15673.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle cb3b270dab69e86c68c33822f231e290bb02fcf66016f045a3dd93a1a2667e1b; original global index 15874.
def localCycle00082 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cc17bb9033bb7e52aa929bae78ada24c9836e2b2589fc075ad5eb2eb9313dc96; original global index 15950.
def localCycle00083 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cdeb8434fb5302096b2118f1d491b923fa9d0e714e8a7b0173194e8979143521; original global index 16082.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle d5b4b2de133eb86c2e7f1bc6c4944be1a06471359b08167fbcd3eed601a00296; original global index 16682.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle d971d7de2cded3412e343190e6251c9af6307235e1fb97b17e4b7b7887536e49; original global index 16994.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d9dba1f28490268dd081abe8eba3b8e1537521cf4946db6c9fb269a5ebf82cc3; original global index 17019.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle db1329df7fe28b95d9eb29641c27ef245f8eb904a7bc81be399d32e299cdad66; original global index 17119.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle dbf5f6452f04fa09e2496f883833472b4ca208f695c39ff93cc1e4990557daf8; original global index 17192.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle dd72740fc451e487445d50b903d41790c74bb3091f1c5c5a78c22a37f0948bb6; original global index 17312.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dfbf8201862e3c6011f5a60e5a0b34ed5317e8be61d61e883622eeb3e94761fb; original global index 17479.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle e30b74290ede37badf916ca51bc24f2ecb1b5bcfbe8dd3efc8e7d5bdfce8c6b5; original global index 17755.
def localCycle00092 : Cycle where
  length := 14
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle e6c0f46995b5d037e161bd37530eff6b6d1c004a189c3945afc30865991efc4c; original global index 18048.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle eb48b13dfd1c5c39a9ad401a7e4b0ba07aef360aef6d12ba99265bb0545a8739; original global index 18369.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle f0a986f10769885be27b9fb8f544f4df249c6a24e9a918ffd224e37242937e35; original global index 18771.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f18e25a31453950acb48f67f2125517b803ba4dfd460a678987e8c3b7d54c575; original global index 18833.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle f57e2a7d1ef90b341a6a0622c0980b6068a7c4a6f5abf164b5eb979617eafd74; original global index 19141.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f9b6db5f84c472e13f18eb52574faf9af29e69ee42bc0468f9a8a61853946538; original global index 19467.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle fcb3c339ac18f884de0fe3b1fcaeecb45cb2a60807b8ba50866564b9aff19214; original global index 19745.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Original cycle fd8c0c1faf57d279c0f70737e421701f39f67c6791f4cef210c2da44832fac48; original global index 19816.
def localCycle00100 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle fe0c3730a96c75a3121a5bc684a21d7f3bbff2295e3d9015165e6863c3a5017a; original global index 19852.
def localCycle00101 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle fea0704e8651915ea5db4c4dbbe4e7e84504267ef5a5b2eea8d201d8bd4adecf; original global index 19908.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

def library : Library := fun id => if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 77 then (if id < 64 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 70 then (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))))) else (if id < 90 then (if id < 83 then (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))) else (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))))) else (if id < 96 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))) else (if id < 99 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 5, 1, 4], ![2, 6, 0, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 5 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5504)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 5, 1, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 32 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5505)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 3, 4, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 5 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5506)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 3, 4, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 32 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5507)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 3, 4, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 3], ![6, 0, 2, 4, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 9 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5508)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5509)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 24 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5510)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 70 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5511)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5512)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 24 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5513)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 86 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5514)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 58 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5515)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 6, 3, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 51 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5516)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 17 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5517)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 75 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5518)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 18 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5519)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 6, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 18 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5520)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 18 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5521)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 34 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5522)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 4, 3, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 23 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5523)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 4, 6, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 65 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5524)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 56 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5525)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 83 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5526)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 4, 3, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 15 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5527)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 101 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5528)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 8 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5529)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 48 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5530)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 50 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5531)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 64 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5532)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 2 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5533)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 67 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5534)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 3, 5, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 29 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5535)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 100 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5536)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 78 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5537)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 39 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5538)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 78 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5539)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 69 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5540)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 61 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5541)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 38 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5542)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 99 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5543)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 3 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5544)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 99 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5545)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 47 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5546)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 102 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5547)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 102 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5548)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 37 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5549)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 91 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5550)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 56 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5551)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 94 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5552)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 73 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5553)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 16 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5554)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 22 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5555)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 6, 0, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 93 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5556)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 66 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5557)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 4, 5, 1], ![2, 6, 0, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 85 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5558)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 85 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5559)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 4, 5, 1], ![6, 2, 0, 3, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 33 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5560)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5561)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5562)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 54 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5563)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 35 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5564)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 1 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5565)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 5, 6, 1], ![2, 0, 3, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 89 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5566)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 19 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5567)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 11 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5568)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 52 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5569)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 80 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5570)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 46 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5571)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 96 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5572)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 4, 6, 5, 1], ![2, 0, 3, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 4 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5573)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 0, 6, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 0, 4, 3, 1]], proof := .tail 71 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5574)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 4, 5, 1], ![2, 6, 0, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 14 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5575)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 21 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5576)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 4, 5, 1], ![2, 6, 0, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 77 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5577)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 77 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5578)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 4, 5, 1], ![6, 2, 0, 3, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 84 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5579)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 0, 5, 4, 1, 6], ![2, 0, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5580)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 4, 1, 6], ![2, 0, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5581)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 1, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 28 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5582)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![0, 2, 4, 3, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 59 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5583)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 40 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5584)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 4, 6, 1], ![2, 0, 5, 3, 6, 1], ![0, 2, 4, 3, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 36 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5585)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 5, 6, 4, 1], ![2, 0, 5, 6, 3, 1], ![0, 2, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 1 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5586)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 5, 6, 3, 1], ![0, 2, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 25 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5587)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![0, 2, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 53 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5588)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![0, 6, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 6 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5589)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 0, 2, 4, 3, 1]], proof := .tail 7 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5590)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 5, 4, 1], ![2, 0, 6, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 2, 0, 4, 3, 1]], proof := .tail 76 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5591)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 0, 6, 5, 4, 1], ![2, 6, 0, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 2, 4, 0, 3, 1]], proof := .tail 97 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5592)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 0, 6, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 87 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5593)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 0, 5, 4, 1], ![2, 6, 0, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 97 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5594)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 0, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 68 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5595)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 0, 5, 4, 1], ![6, 2, 0, 5, 3, 1], ![6, 0, 2, 4, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 13 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5596)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5597)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 95 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5598)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 82 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5599)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5600)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 95 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5601)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 74 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5602)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 6, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 63 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5603)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 81 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5604)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 3, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 49 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5605)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 81 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5606)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 12 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5607)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 81 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5608)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 3, 6, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 26 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5609)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 6, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 79 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5610)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 41 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5611)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 62 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5612)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 92 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5613)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 42 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5614)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 43 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5615)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 8 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5616)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 20 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5617)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 4, 0, 1, 5], ![2, 6, 3, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 27 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5618)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 72 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5619)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 98 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5620)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5621)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 0 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5622)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5623)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 0 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5624)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 60 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5625)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 95 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5626)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 10 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5627)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 88 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5628)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 44 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5629)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 45 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5630)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 88 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5631)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5504 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 5504 ≤ id.val) (hhigh : id.val < 5632) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5504)) = true := by
  let j : Fin 128 := ⟨id.val - 5504, by omega⟩
  have hsum : 5504 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5504 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard043
