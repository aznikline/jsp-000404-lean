import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard044
open N4R2RowDataReplay

-- Original cycle 003b2a847a1d270489eca46c2dd8a9e1fe6a4a08d623d850fe06fb16d037fbe1; original global index 21.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 00faa5294fddde18cba3128f568f70d9d791f17345c504fcd69055fa01a462b6; original global index 85.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .gapLower 5 2, .gapLower 0 3, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 012f1a055fc6b8c830f06ea9d549edff13746b4c2279e1d057023b944336c73e; original global index 105.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 0392e1e4bca978ce5f53586037e6fc5fe7f4a030b2dfa004011085a6cfdf3ea7; original global index 287.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 049ed7ae8e691f0886a06e7540862b9d4c0ba5f2295b270d3a113e19872e91b1; original global index 366.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0615ce55007f2a96b482f24a8e690b68713e7f8126340853985e059d44d066f7; original global index 504.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 08673b9a255f3990c721a202ae408c6edbbc5389ee05a9f6c09424ada73abc15; original global index 668.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .gapLower 5 0]

-- Original cycle 09b5c9ff69bc9ec1804ea70baed9173fd24b1fc7597b4d07e0ac151973018f11; original global index 775.
def localCycle00007 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 09e8c47278a18a862584209f72ac828f3fac984cb22d6ee8016d96b5deaf6f2a; original global index 798.
def localCycle00008 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 2, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00009 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0e5c6ee40334a92db10fedf2a7b007f3c5b635739e9933ed19fea085ed9d5d7d; original global index 1135.
def localCycle00010 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0f1d74c5d2f83e2a7073ce4fbb15e2cc7a7c1d71fb66155d875c1e35a4c10449; original global index 1202.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 102100dc3dd5f86b77920daddb636dc1d58180dff2a04bd4d68024d8f032c73f; original global index 1293.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .gapLower 5 0]

-- Original cycle 1126da02c6123fbb406b65da2289ebbd106debd7685243be805bbb6bc81a2269; original global index 1367.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 115f5304490562a1edcc556fa6222420cf8f4f43c59bef2778abbf20ef250e5d; original global index 1383.
def localCycle00014 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 6 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 11e50096af3618e06ea239c46801dc6551919ee26be9bc9a94c9db37b0431305; original global index 1431.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 1230a6794fd520bb3338bea18559bd069c91e70fcacb9213d743e7e09697a08a; original global index 1447.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 12bca2ae91fb9f6892596455c0f0e5959780d846af206c29df7a9a574b46cd91; original global index 1477.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 14d909a310ce4ab57f7c6fc53db8d2ae18bbe1e7da84dafeb19f4beb2ee8cede; original global index 1654.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0]
    constant := ![2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 8 1, .gapLower 0 4, .triangle 12 1, .triangle 9 1, .triangle 1 1, .corridorLower 0 1]

-- Original cycle 172ac9cdecd3e50f0b6061abab368d40cdec5feb201b05d7a761249a2d2557fa; original global index 1820.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 1a78f7af680aac56d014fc9ac3997b2ceb4bd34a2b1044526792f3676c43df19; original global index 2061.
def localCycle00020 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 1e2b71f5c26efd13ce612a923de059af60607b7ec446ff7e76af180f46ed84e2; original global index 2319.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1f6cfcc815e07281d5d18f90fbce603be31113f5b2ab4c4d312b9bf1445b77e5; original global index 2413.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .gapLower 4 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 209bf5bf20c74584919b7ddd916b966b44caa8f08f4f364411170e9b6624ec41; original global index 2501.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 241eb5b62fed0e9e3bed4c1517d40c928f4bc0ec92d5ba3c8a3421d80d54db9d; original global index 2767.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Original cycle 24e68ba16ba0fa6ee8fefb4d55ec7ba44832c50b7fec1fa30b2a59b857feaf0d; original global index 2832.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 263688987147e4cdc66ecb4d85b67067dc4c72713d793a9ffcd5b7a87968b023; original global index 2933.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 2939c0e8c626b661fc5d62c05bffb0f66c6f582907dca653b463265d2ea34cb5; original global index 3146.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 297233fb8bc00957b548f5736f45fbbfc1bccfc701cdb808678707cad70f2953; original global index 3159.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 2d7b3d2b4d99ba6e356039e506c1b5f2581a64ea299bcb033d25bad182b8e2f3; original global index 3468.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -3, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 2ec95d07c628a6ef6fbe8fefcb7cbe8ad69e6028e4c9c8e006b51c1281e41a69; original global index 3579.
def localCycle00030 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 5, .distance 0 3, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 14 1, .gapLower 0 2, .corridorLower 0 3]

-- Original cycle 31885c9d1124f033d9d79b67ab4eaffafce3871732ec64f0b25497b15fc9be96; original global index 3777.
def localCycle00031 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 2, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 32c15589185b66a36322e4dd5300d55364ea173b7d86421bd24876ff4a47b719; original global index 3887.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, 0, 0, -3, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 33f047714a01fdd3f35bea27bd41b0aafeb0c75b43e62efeecfb2de94d60afc2; original global index 3978.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 33f704a199413fa5b55b3af0c0ca189c8f789875d988608996ab28fdf82e5f4f; original global index 3979.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 35fa407e7a308b8b84482032b69303c886cbb1c28d87febef6fe256e1b115e22; original global index 4143.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 36c876e486aec848fd58333f79aca266f245b6c05475f8a44b55984e1404c00f; original global index 4211.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle 372f3221f97c9178f9d2b7344d3a855120ffb50f81d01526041efaae13b4b3a8; original global index 4235.
def localCycle00037 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 385e36175a938e5b4e43413e9988b0014728587709f9b0bf49acb21b275651f2; original global index 4331.
def localCycle00038 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 38a412a79aaab04d02a984687b1a781389359feab5d3dba8bdb464be053aaa49; original global index 4358.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 38c0a7576de9cb6343be6c63d67bd7f43bec3049e4eb64e1427d7ace550ae02f; original global index 4366.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 1, .gapLower 6 3, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 3a1ca81e17b251e7250d9f2c7d5d7ffcb9155e1b4b15cd4848d9bee25a51ae92; original global index 4485.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 3a5d1075f423b0cdd37bbc8180c52206ccbe7e1d72d4347eae5d3b93b52f4837; original global index 4507.
def localCycle00042 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .triangle 9 0, .gapLower 0 1]

-- Original cycle 3ab678889d04e66609663db8f01044063d5577a643b81fbfc8cbff80b114752d; original global index 4532.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .gapLower 6 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 3d825cac7a19c623644e96c583c3c36f3baa141196da721836c13d4552fb1c50; original global index 4761.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 4097ea5ef57fc87af0e464a01eaa1e928b53fc89aa8f4109435db19653713664; original global index 4993.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4266f674f2d15693ad794248722a01c1abbf78f114eecdd1a85fe7d33c5e9817; original global index 5116.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapUpper 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle 42a9e4de31121ff103c753e84bff9734a72b5933dbc562c19f15c427092190a8; original global index 5133.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 42b881e596fce5f122b5c9444d20248f1aebf52d9f002dbf9f77366efc4f92b0; original global index 5138.
def localCycle00048 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 12 1, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 438818266c0af205e97eac7dc95adfb33349a3b8b488077f947150d73e0f9b3a; original global index 5222.
def localCycle00049 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 43c200ddb7a83daba17df148221aa490429573549b4ea2a465362a2273ebe8cb; original global index 5242.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 44275a65a70e8be898025f09020d0ded3e68999824bcaea51565f0a750fd344f; original global index 5275.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 4477614c97a43e3517c81ac7dbaf18c721318d4a0086b5a729d315eaa9c5d478; original global index 5297.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 45fc028eacd876a725098382417da63b239fd517a45e16f6cb48dbfe2eac75f8; original global index 5414.
def localCycle00053 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 4 2, .gapUpper 2 3]

-- Original cycle 460b2f8d3e4b44e7884c70f5c4bf3eb55800e64555836f84c54c90385aa82081; original global index 5420.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 48e0022ecd366af2646c033ef82e84c679721dc26a68e03a6312a28028c0175c; original global index 5646.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 497db7e8ffced3ed2d23a8a264d857ec77ca88a8f328f2b26bae4cc5eea0170f; original global index 5696.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4ba269006edc5d1a7aea93c5671498021dedcf981e80ac474a5a6aab76b96c28; original global index 5867.
def localCycle00057 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 7 1, .gapUpper 2 3]

-- Original cycle 4c11eda616a61cd4bcaffd171d3401c3a2489bd387a6bc6328ce108e1522de71; original global index 5907.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 24 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .gapLower 5 0]

-- Original cycle 4c350ef7a378dda33b924f3680939f074a1a47fd555b88e6b1b226e601cb8bbc; original global index 5914.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 4c67bbe1f08ec235c237d908e875a063a80429808df5813bc09f24a91ac1acd6; original global index 5933.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .gapLower 5 2, .gapLower 0 3, .triangle 2 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 4ee862cf08a19987a51b2a6e5418af9f35490fb9b6806ae99a6c4ece35c1d27e; original global index 6130.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![4, 0, 0, 0, 0, -3, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 4f0876838b15fe7a9810803ea66fb6c0f17f35c97c5c3ea89d887d3b00862cd6; original global index 6140.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 21 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 508d23b7586030887525366d78c9acc811be85092a52106f2ebe05e866eb6b25; original global index 6254.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 517bc8b868e9c7d8b4c72cd54d7227205fa93a93d1e21be8386ff6687cd5e80c; original global index 6337.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 52446932c711798105803143db6f7d234abc64a62d20e15cdfe2d30c8280d6cf; original global index 6396.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 5268be867dbebe67249e0b3677f4a9e8459e7969235881ae1e2ba9a705eed793; original global index 6408.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 52e49017f105df2955d3f731fdad2410cb274b7a6a3e641a67c7929a47cf7612; original global index 6454.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 55472f0421abc85af0cac985b8406bf2947fff673f93a9fdd851dc96591003e5; original global index 6602.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 58ca7ddf74feda1382c28f3c64ead32b2c125ddcea7ad0ce95d316b57a0741af; original global index 6887.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 59463b87781911b4f90258c20ef52d1c5496686739aa0c0b56c7fcc696294b43; original global index 6926.
def localCycle00070 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 2, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 5a68e4d6b9ec155095547b46224cc3003730432aa79b5e14d5ac7b5aba80bdfa; original global index 7037.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5b272cde9add4d5f617ce7a0a29e6bb569423f25cb9cbafe846e671cdd2a27a8; original global index 7095.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 5b3b4f780b47a04bdbdf08d3ba817566a6cf468a3f0d33f27dcd8c1ac1e37de4; original global index 7101.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5c298ab48add7a660ef9bec979cc2df0ca4f19deb8f49741b1ed2652aa7afc90; original global index 7176.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 5c761fd9b3755a2dd2d8f6c17bcdf39689589ad1b3a3d65e14885980bf811678; original global index 7199.
def localCycle00075 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5d085b21a81f09f6aeec16f4fa7cf362f5513b1f8974fa35f7fa18003903382d; original global index 7238.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5e61cb079ef0ccf857c0f0af5b7f81f9f2cbdb27fc4b617731286bb9bf001746; original global index 7343.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5fee8eaea7bc333d920db0e404a561a0197bdf3e791d1151b2be764c1ad2f6d2; original global index 7480.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6083a75b31add0860536f9e7a5cb4d34662dd7f782daf157b34cf876192095c8; original global index 7515.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 60aa9c70130aaac5a49022c6fcebad622fbe757dad7a8eaef2cc7e15de9dae71; original global index 7526.
def localCycle00080 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 5 2, .gapUpper 4 2]

-- Original cycle 62ba464bdc27e9ee62d08fc243ee73eb836ec24603d56935d999e27795eef49c; original global index 7705.
def localCycle00081 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 5 3, .gapLower 6 3, .triangle 18 0]

-- Original cycle 64a6ba5dd5fce360220a7605b2afd067749b715df3346cf517da70d4b3d80f5b; original global index 7841.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 64da7214b4216cc7dc428bb77185d29d1f264900796ce6f670ab0e40b1f530ce; original global index 7853.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 67335d407e25d404fc8d983c9f88f5df36d66f094e37cffa7a5525acbb9bd1d1; original global index 8022.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 6abc093f514cc7a322786a627a663717f4e04197bd6febb336e932ae6461cc9c; original global index 8309.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 6d2b8030ff2f912d3d0208aa369d6f427188e5d2c2baf0f39cae3efc075cd6d2; original global index 8492.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6efeb1f174eb3cb9fe77050afa8c45c2e3214f9d830af646ca19a944a26f5701; original global index 8609.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 712151cf1283c77cf0487e067b9f57d98878cfd3d2330dd3e9f43e7ad7e614fa; original global index 8775.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 0 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .gapLower 0 4, .gapLower 4 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 717bf4d48de7070d481356211bfd1bcfd839e1568c1eab778f29e49ed3172f62; original global index 8806.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 73136d601c5d4abaf9f458444c497f9e2e3d084c25ee8ad7319431dce541707d; original global index 8913.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 743078e394c2892212708f8403e151d5c99d884a70642358bb47f2835a476eb2; original global index 9015.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 78565d8f2d4749823cb72db3ab526c66f7487cdc5a4f9189b50d84eb412e3604; original global index 9302.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7886a275b5935a2d63c5738292fd21a42228afccd9669b3d8beed6ef651bff1f; original global index 9325.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 78aabe043254b15b044ce321fe503ddfb3b90cc254d7a02956c676bac22e6a1e; original global index 9334.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .gapLower 5 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 79aa62c171e2685ca0d1be1c565229bad6ba9751115157fbdbcdd200f9debdab; original global index 9411.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7cf406f6ff441e3075d96664c9abe72b276e1021ad514254581a058e097335b3; original global index 9675.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7da924e2c6c7321ffcf2bbd03824b8032f4cc2e9f18484dc5262740d55cafe36; original global index 9753.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 7ff5b8ea7b9115637f2856ecfe2095674cd2d43f5d84e8fa15560074179930a2; original global index 9928.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 802c403958b46b780874ca53320821247f0a48bd478ffd215aff5c650de4921d; original global index 9944.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 80b1fc6d71bc32710c07dc73b0119a2d05a91400803ed9f1e10e227140968479; original global index 9993.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 7 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 816303c7bcafd778bb1edcff627920de3abf5e1876a77a09b34c606b6631db81; original global index 10050.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 81a5f66ea9bbfe0d6dd7e77d222ac40625a9c4bc121be1405ac67c283129c778; original global index 10067.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 8272085ffbf9497d9128a96f09f1be04f835a191384de8c30c0eb8a1d2928fe8; original global index 10123.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 2, .gapUpper 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle 83e3e31e148fcbed26123e2b84f54a877491e2f7ad5697de67addfc9d4a9a241; original global index 10238.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 5, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 2, .gapLower 6 1, .triangle 8 1, .triangle 7 0, .gapLower 5 0]

-- Original cycle 84c19b037a5ef4a4d90d7fcd1d48a1c0128615932377bce3bb16af1c9415788e; original global index 10308.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapUpper 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle 85256390cb2b15af61a9b40906c2acfbc4cdfe68b2ef8d37719736d59ed54c6d; original global index 10332.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 86279b049440d3dfc816cc963e3739b1ded5424b27f4e1bc080d6b8321be75d2; original global index 10405.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 878fb9efa742f9775c292f0f8f0aac146491a14d42f69dabd8f8f21ab970c725; original global index 10511.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 87cb43095da5e8681365aadccaeeeb005e8ba7b5df49ea326d052e482e97327d; original global index 10527.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 89e01afca9007859b34e04e11fd2099a1ec29ac1c557207e1268999e036b4335; original global index 10683.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .gapLower 5 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 8a579c2df132e1b17eff3c8e1bb1dd90197f76f5138b7638aefb7a80e7ac2267; original global index 10720.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8b3ca189173aa1e048750a8690914fa735f0c488559cb8378c1195630411444f; original global index 10787.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8bb876ec730ddb29aaac7b1211d51d9134d62d1e676cd63837cdfd4a07ddc093; original global index 10816.
def localCycle00113 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .triangle 9 1, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8e5e02a9b0e1b715902c42fff5e543270d1d8849eea3a1e4144869cae9d0420b; original global index 11020.
def localCycle00114 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true] }
  origin := ![.gapLower 0 4, .gapLower 0 3, .gapLower 5 2, .triangle 28 2, .gapUpper 2 3]

-- Original cycle 8f51b8aabc70148827750c18be7a02054905414c9b970b96a8735944c84aaf85; original global index 11091.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 93674c84354cffe64794ad68669cc337cc332c4fd492bb65d60d84409e446c64; original global index 11433.
def localCycle00116 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 5, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 4 2, .gapLower 5 2, .gapLower 0 3]

-- Original cycle 9463bc8f8e4267305ec789c7037bbe68134a4b1ba01e4d22e58832dfc6e53d2d; original global index 11516.
def localCycle00117 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 94ad2eb27bef17e74e5c465555755c5e17f67b6dd1d21b531647555964f3c2c2; original global index 11536.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 2, .triangle 8 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 94bf6ab5821a3fdbf4626e3fdfd5d387946be70c7520873e113b038da220d202; original global index 11544.
def localCycle00119 : Cycle where
  length := 16
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9560d73d43e7afd3a2a6442e716ad1098f1eabb9d50451b8b004ba8f87697839; original global index 11610.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 96dda04f9b69b089da7aa0b8805119917a3792a1c266c377721eda763e5e99bc; original global index 11727.
def localCycle00121 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .gapLower 4 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9916b1734150d7af09f60227c75cb5ec377f16ab714ef2af35653006a5d8597f; original global index 11887.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 995a14fb0aad1a8f928f9a5f05044afc948730a1db4974e86607812c1e301417; original global index 11906.
def localCycle00123 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9a235a96b1cbed432139db354c9b8fab0af28a268a9e100d127b4b7721ce6b5a; original global index 11969.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 9a65a14fbff266985b4937ecd126e8db9cb16e60b2cd76e25fafb169870eafaa; original global index 11999.
def localCycle00125 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9b42e611b850015197f37ca825e4a0927689dc897c64dcc0431a4c7966756925; original global index 12073.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 9d485d9dc55734448bba2cad3aea803c1e91da0b983f94324d38b908812a205e; original global index 12235.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9ec0f8681ecd4751852899d1c80fbca6076fab9433351267e5f1aa820e316daf; original global index 12360.
def localCycle00128 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9ee4779df8f12248d2a588ddaed2d59409637e59c66e10a0012478250dc9ff21; original global index 12370.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 9f7197df8cf397bd9302894cb0b0fe21fb36b3cae82b83f4e939a89fab46c366; original global index 12409.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a3928ebf929ad770c76cb380eef19e770c638b3a1b1037db4aef5538e048be58; original global index 12710.
def localCycle00131 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a39bacc542b8683191fdfd067af52eaf6ae788220db9b2f4ee602ba8feac490b; original global index 12715.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a3ab91cd18f5292cd0abf6d1c7612e3f4ac945cff10e3a5cdf0aa2ffe9a7c89b; original global index 12725.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a5008154767218b75e26b5b414c1a69b39989bbb89e326ec79ce71396a250c97; original global index 12824.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle a6e4583eeb1fe374b786923a77fbf14e372e10bc6f29a6b96da409e3d45330b2; original global index 12963.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle a6f2c963ebdc46663d9f9cc698bcccd3b8c6d9017557d81a299581f2b3da398a; original global index 12971.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle a722ceb91e09b002a7c95ca9d2548aa29a940f8d833cbd16e0b2544f0c277459; original global index 12994.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a81152e799cd8bb4a915a6c3538da0939c712464d6a5e6fb7fe3b1426ad05289; original global index 13088.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .gapLower 2 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle a9b93cafd537a58f2790a49739a0738d2440a0d9865515c4e39867bcf0c1807d; original global index 13213.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle aa3a283bdf9b94af442990a01b1ede175064fb1703cd4735ba9fa32ad2687c3e; original global index 13252.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 0 2, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle aa91d4599a677ffd67617e660ed5284686646b9232966d56a501496defb17149; original global index 13287.
def localCycle00142 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 6 2, .triangle 18 1]

-- Original cycle ab52a8deaac29aab65bf105b88dab1d0fdd91b6e9776f147bac4294d49f80cd0; original global index 13348.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 0 2]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 6 1, .gapUpper 2 3]

-- Original cycle ac53257c9cc1c8e8c5c509ebeef94cb21a2d5740b353741dc85ed6878404df32; original global index 13434.
def localCycle00144 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ac6bfa2927e76e345d5de2e355648fdc275a9143cf44c7625695e4a13e79028f; original global index 13439.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle ae6c23255d2bba23ef8facf65ea2e9f341c747c6bb5c5ab562ebba6c2df5c0fb; original global index 13613.
def localCycle00146 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 6 2, .gapLower 0 3, .gapLower 5 2, .triangle 28 2, .gapUpper 2 3]

-- Original cycle aeb8b5c518d91773fc826699d45e308330cf34ecf7c865ae6717bd4829450c06; original global index 13640.
def localCycle00147 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle afe1f1ab78b04c74a8971ace8e699178b84e71b5aef63a436ce2dcb8c10e7d6e; original global index 13737.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b0a65d5ec74dc3d83775ae3456745dfc09969d4a1dace3929e4ec8d8240e7787; original global index 13793.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b37920ba1379298dda77e28a4a63b6f4a63257a4e1e71b654a563faf9c19488c; original global index 14025.
def localCycle00150 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 4 3, .triangle 9 0, .gapLower 0 1]

-- Original cycle b3cf4a2c68c867b4f8ba1acf866123aaa01e34b0f9275eede2337f75b4941ec8; original global index 14042.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 7 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle b516e0be51347638a437a38e5e510128a8118277e3d90ba76aa031cdf1be20e3; original global index 14147.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 8 0, .gapLower 0 4, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle b51fdec28e4e021ae782178f9f65f5b19a0d9ab1b78abeff53950f1b53aac7e2; original global index 14155.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 2, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle b6c09d234d0eb8f11e0e5192dae29c24d25edd034576adc35f20c8e26c488964; original global index 14282.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b8e84a339343d8f339ffab9a7b58935208133209d7c39e8fad7c161892a276fe; original global index 14433.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ba52643fae7d89b284ce2401ab0d2c6c2643ab595c7dfbb05cb35eae0f88664b; original global index 14548.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle bea84193333821e33ab18b659d9c30b275a2a834edbe7267cef96d224a80ddac; original global index 14873.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle befecb0f8441e2f3f5fa3399baf1fbb3cf839f882a589c9ea51df7df8b77e235; original global index 14902.
def localCycle00158 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 0]

-- Original cycle c610d7abf406ec57b70c18a4a4fde3bb3875a887da8cceb95f77ebbb092cc65d; original global index 15448.
def localCycle00159 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle c84750d9f721524e9f6b02d32024484ebaecef1f34ec0c694139a868a96dbaeb; original global index 15631.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 0 2, .triangle 6 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle c9346653f2c7928a8246b98a4b86052e74f05d7be4c34678956f312b621b4f1c; original global index 15724.
def localCycle00161 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle c93b9808b101aaf2e2376409af5eb51434f0a5b60467bc39f3096bfb571d4e9d; original global index 15729.
def localCycle00162 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 5 3, .gapLower 6 3, .triangle 18 0]

-- Original cycle cc5b8ede404437d25b0677889b546c24c18039fe43af89e4936b278e5c7b69e0; original global index 15971.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cc6f9877cca4f8a52379e80d75f24d03a32773b8261a8942b717c6689ab4c5a8; original global index 15978.
def localCycle00164 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 5, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 13 1, .gapLower 0 3, .corridorLower 0 5]

-- Original cycle cf002dfe8e042812317346e2b8f8b27f05cfa698e3059dc15972c6f69f56d921; original global index 16153.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 8 1, .triangle 6 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle cf36fa1285d1e5b25b8f38e17013fdb81e635123a3805d648a808e2abae8f67c; original global index 16173.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cf9397d1d913cf5c4ec5ea2ff4ee9afecb689982ea7b804fcdd28ba84f1fb92d; original global index 16194.
def localCycle00167 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cfedc7fed7a8e2be4d0da50c005ede942e7d07bc55db1b2a195dcbae1d4878c3; original global index 16225.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, true, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapUpper 2 6, .thetaNext 1, .thetaLower 1]

-- Original cycle d1537a634332c1f921b4f496e57cd4178c3349c4ed3c3155e5699ea8d1cfa440; original global index 16338.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .gapLower 3 3, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d187f77905b5e82dd34466168dc9351f5bfb5c588d1487d2e7f7bddf6296e8ba; original global index 16353.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d2fea683287af5b80ae7ad5f515c2b17f921e4122a076a8b4a2c8bce5344f38a; original global index 16457.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d3b08ff33a2ff72b66d4829f7a784358cfed506c8611b3cf63ed20d5e06799d9; original global index 16519.
def localCycle00172 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .gapLower 4 2, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle d3e4e766552ac83652c3ec4a79e4a37f4adaaeec039f9fd8e8d160e911a39a53; original global index 16539.
def localCycle00173 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 2, .gapLower 0 3, .gapLower 5 2, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d514ea78caa13f27df55697a6423df6e3755a2d66d3d6d97b7d4dc7dea2c439c; original global index 16628.
def localCycle00174 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 4 2, .gapLower 0 2]

-- Original cycle d61548c9dcfa6204acac78772023980e0bc2fb60269cfba12e5bdeac74c62ab0; original global index 16710.
def localCycle00175 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d6b21082ce42b8ecb9b8f786fb1c0a2ea687c0c0b771c7efcdeb910ba943b7c7; original global index 16758.
def localCycle00176 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 4, .distance 0 5, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 2, .triangle 12 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle d6f79000f382e4946d211cb5ff77208a92e3f5dfea6fe4e837e4cbad9a9865fb; original global index 16782.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .corridorLower 4 6]

-- Original cycle d956dbcb74b4f65dcd2ca356b828dbd76dcd3ae6fa4ddd1f9c07c716520e2ec6; original global index 16985.
def localCycle00178 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d9e5cdcf24a4ad0c3f75f2aecd689cd462422a2811f2b084af0872425c46cb94; original global index 17022.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle dbb1d36948b81c60165b1476fe77ac855daafc02cee0768a2ddf8d4b93d56872; original global index 17169.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 5 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 2, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle dbf915d41c26af1817670e3fcd289f713a3ccd5a39409d28d2f96f457c421f34; original global index 17194.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dc563c98f206da8d17088ba849e70023493fb24adb115b60ac80ac0315709d50; original global index 17219.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6]

-- Original cycle dd72740fc451e487445d50b903d41790c74bb3091f1c5c5a78c22a37f0948bb6; original global index 17312.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ddc6ee3311a9a1dc61c17d7f2e8bd530c880e02a77bd078c87e4db72b79615dd; original global index 17336.
def localCycle00184 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 4, .triangle 12 0, .triangle 28 2, .gapUpper 2 3]

-- Original cycle de53ab5ee1b7a27aaa81028acca09737e3de80d04b01d18c2944d392f3eb8303; original global index 17380.
def localCycle00185 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle dfccb9b4550f84967d1535345c53a90ad240f2cd75ada0b5d39515c35d5cca03; original global index 17485.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .gapLower 5 2, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e00271cbca8a6e3bcd0579808987d091749d23b6544f46c96596c7410d642821; original global index 17510.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e0c3fbe6ababd51378c827405fccadc538480a7291af7a13e7836f26a89a7d4a; original global index 17574.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e2b924d68d66386dbff0e38637964d4d84a40ed39fc6fe12e7abaea7ce84eba3; original global index 17732.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle e57785abbb5ce0a40b66744a344a0497ec27e7b714e9502d85192fd00302041c; original global index 17945.
def localCycle00190 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle e77afa00c164932e4b80774d8fdfccc74fee8a3628c30a2a5e4d151a6c75ad03; original global index 18105.
def localCycle00191 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e7a45e9db75cee71f81f4eb704a0aae7c2382b9388832270eeba1b9155716cb0; original global index 18117.
def localCycle00192 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 3 2, .gapLower 4 2, .gapLower 0 2]

-- Original cycle e880904e838327eef86313a55a7b4a5e7b5b147d6da1cee9630352d7523b16e8; original global index 18173.
def localCycle00193 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 1, .gapUpper 2 3]

-- Original cycle e9d86599a9947a5c11355bf9cf06f2c2d69e79d048ebe369ca4bbef7d46aeaa9; original global index 18270.
def localCycle00194 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ec968939bc4af53f02dadae825cd22e0991c59f561eb9672c0b9946034a486d0; original global index 18471.
def localCycle00195 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle ee639fe3505fb79702cb229643469bc40b62e73c8ce217192615c30f1d745f72; original global index 18609.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f14c40b916271c95d300e4f3346cf5c7f12b12a9dcdca2f4cb4519a4abf4edb4; original global index 18815.
def localCycle00197 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle f47531a90ad0981ddc05c7531d0a10c239450f177273eac3edf26d8e950e8b9d; original global index 19061.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f5cb0d8f1edb652ccff7498deb0c8124cc1ec8f6365dbb9acaf38dcaa10d8bad; original global index 19176.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle f6ff419ba7199f58e172dcb897a07d23599e8c32a821838c72117e99556d99c1; original global index 19264.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f8467bcc96fb043de50eab0f0d21b38c2a62cddef666a4c39180133ecd194a4e; original global index 19363.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .gapLower 6 2, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle fa0b9e629dba5473bd84a97a52f14ccf350f3d22a9154dc329116e0fd6317860; original global index 19497.
def localCycle00202 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle fae79662be791a0211f599852620ea5044c9d024aecd87cb3ef516df9378d453; original global index 19581.
def localCycle00203 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .gapLower 5 2, .gapLower 0 3, .corridorLower 0 4, .thetaLower 0]

-- Original cycle fdd235577d90d0187ad745b63034e611b6ec571fa7bde3a48604ea19c9ead2f0; original global index 19838.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle fe6e7dfa17cc0d64e2e1abe581d9aadfd16c44c9124db29c020c1acd2819211f; original global index 19889.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle fffb1c66cf2344891eb9ca27c1dd411560299a35ccad1b6ab26c305637932fc0; original global index 20025.
def localCycle00206 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 4 2, .gapLower 5 1, .gapUpper 2 3]

def library : Library := fun id => if id < 103 then (if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 77 then (if id < 64 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 70 then (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))))) else (if id < 90 then (if id < 83 then (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))) else (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))))) else (if id < 96 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))) else (if id < 99 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))))))) else (if id < 155 then (if id < 129 then (if id < 116 then (if id < 109 then (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 112 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))))) else (if id < 122 then (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))))) else (if id < 142 then (if id < 135 then (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))) else (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))))) else (if id < 148 then (if id < 145 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))) else (if id < 151 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))))))) else (if id < 181 then (if id < 168 then (if id < 161 then (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))) else (if id < 174 then (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))) else (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))))) else (if id < 194 then (if id < 187 then (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))) else (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))))) else (if id < 200 then (if id < 197 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)))) else (if id < 203 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 92 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5632)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 6, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 15 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5633)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 90 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5634)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 134 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5635)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 119 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5636)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 109 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5637)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 109 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5638)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 125 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5639)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 87 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5640)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 49 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5641)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 205 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5642)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 0, 5, 1, 6], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 196 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5643)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 4, 3, 6, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 196 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5644)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 4, 6, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 196 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5645)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 6, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 77 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5646)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 135 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5647)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 82 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5648)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 5, 6, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 71 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5649)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 17 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5650)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 0, 6, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 96 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5651)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 96 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5652)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 129 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5653)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 171 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5654)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 0, 5, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 41 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5655)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 0, 5, 1], ![2, 6, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 177 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5656)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 0, 5, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 0 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5657)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 89 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5658)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 126 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5659)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 188 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5660)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5661)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 91 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5662)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 115 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5663)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 6, 5, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 2 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5664)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 6, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 194 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5665)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 3, 5, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 136 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5666)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 3, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 194 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5667)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 124 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5668)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 3, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 194 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5669)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 3, 6, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 118 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5670)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 6, 3, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 65 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5671)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 4, 3, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 45 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5672)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 33 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5673)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 6, 3, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 33 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5674)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 0, 6, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 33 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5675)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 156 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5676)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 156 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5677)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 51 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5678)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 5, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 1, 5], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 25 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5679)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 1, 5], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 25 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5680)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 1, 5], ![3, 2, 6, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 26 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5681)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![6, 4, 3, 0, 5, 1], ![4, 6, 2, 0, 1, 5], ![3, 6, 2, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 19 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5682)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 5, 2], ![6, 4, 3, 0, 5, 1], ![6, 4, 2, 0, 1, 5], ![6, 3, 2, 0, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 185 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5683)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5684)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 7 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5685)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5686)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 3, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 7 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5687)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 6, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 127 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5688)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 5, 6, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 91 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5689)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 1, 6, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 35 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5690)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 68 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5691)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 5, 3, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 16 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5692)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 1, 5], ![0, 2, 3, 6, 1, 4], ![0, 2, 3, 5, 4, 1]], proof := .tail 106 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5693)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![0, 2, 6, 3, 1, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 68 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5694)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 5, 3, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![0, 6, 2, 3, 1, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 16 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5695)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 6, 5, 3, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 112 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5696)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 4, 5, 3, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 112 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5697)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 4, 6, 5, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 11 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5698)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 11 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5699)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 5, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 76 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5700)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 76 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5701)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 76 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5702)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 4, 6, 5, 3, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 0, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 200 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5703)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 0, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 2, 0, 4, 1]], proof := .tail 200 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5704)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 6, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 2, 4, 0, 1]], proof := .tail 123 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5705)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![6, 4, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 4, 2, 0, 1]], proof := .tail 138 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5706)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 4, 5, 3, 2], ![6, 4, 3, 0, 5, 1], ![6, 4, 2, 0, 5, 1], ![6, 3, 2, 0, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 170 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5707)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 4, 3, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5708)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 4, 3, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 1, 6], ![3, 2, 0, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5709)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 4, 6, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 1, 6], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 67 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5710)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 5, 6, 4, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 6, 1], ![0, 2, 3, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 133 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5711)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 5, 6, 1], ![0, 2, 3, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 178 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5712)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 5, 6, 1], ![3, 2, 0, 6, 5, 1], ![0, 2, 3, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 95 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5713)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![0, 2, 6, 3, 4, 1], ![0, 2, 5, 3, 4, 1]], proof := .tail 75 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5714)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 5, 4, 3, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![0, 6, 2, 3, 4, 1], ![0, 5, 2, 3, 4, 1]], proof := .tail 144 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5715)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 6, 5, 4, 3, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 204 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5716)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 4, 3, 6, 2, 5], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 0, 6, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 191 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5717)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 120 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5718)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 4, 6, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 0, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 3, 2, 0, 4, 1]], proof := .tail 154 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5719)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 0, 5, 1], ![3, 2, 6, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 120 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5720)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 2, 6, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 3, 2, 4, 0, 1]], proof := .tail 74 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5721)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 0, 5, 1], ![4, 6, 2, 0, 5, 1], ![3, 6, 2, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 84 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5722)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 4, 3, 2, 5], ![0, 6, 5, 4, 3, 2], ![6, 4, 3, 0, 5, 1], ![6, 4, 2, 0, 5, 1], ![6, 3, 2, 0, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 182 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5723)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 148 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5724)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 111 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5725)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![2, 0, 1, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 181 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5726)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 5, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![199, 159, 13, 31, 193, 37, 151, 197, 72, 60, 48, 202, 202, 34, 197, 197, 197, 197, 64, 57, 102, 102, 152, 116, 110, 20, 18, 39]) }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5727)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 5, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![199, 159, 190, 80, 206, 32, 59, 197, 179, 198, 184, 70, 202, 4, 146, 184, 197, 197, 146, 184, 176, 30, 114, 173, 186, 10, 184, 50]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5728)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 1, 5, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![199, 159, 190, 85, 53, 61, 165, 197, 179, 198, 113, 161, 202, 4, 197, 197, 197, 197, 14, 143, 176, 30, 23, 8, 164, 22, 88, 52]) }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5729)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .low6 (![93, 6, 142, 81, 168, 9, 167, 86, 201, 162, 105, 69, 5, 104, 162, 58, 12, 5, 27, 180, 189, 28, 97, 162, 162, 145, 122, 131]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5730)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 3, 6], ![2, 0, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5731)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5732)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 5, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5733)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 1, 4, 6], ![2, 5, 0, 1, 3, 6], ![2, 4, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5734)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5735)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 0, 1, 4, 6], ![5, 2, 0, 1, 3, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5736)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .low6 (![83, 29, 142, 99, 44, 139, 3, 137, 38, 175, 46, 158, 149, 43, 175, 79, 108, 78, 157, 153, 140, 38, 66, 40, 175, 101, 132, 195]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5737)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 5, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 155 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5738)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 5, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 21 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5739)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 1, 5, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 160 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5740)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 103 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5741)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![2, 0, 1, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 130 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5742)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 4, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![2, 0, 1, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 36 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5743)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 163 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5744)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 1, 6, 5, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 73 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5745)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 1, 6, 5, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 141 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5746)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 3], ![2, 0, 4, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 107 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5747)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 0, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 107 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5748)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 5, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 0, 5, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 0, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 160 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5749)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 0, 1, 6, 4], ![2, 5, 0, 1, 6, 3], ![2, 4, 3, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 169 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5750)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 2, 3, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 160 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5751)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 0, 1, 6, 4], ![5, 2, 0, 1, 6, 3], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 55 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5752)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 183 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5753)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 54 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5754)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 3, 5, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 187 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5755)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![199, 150, 192, 203, 193, 37, 151, 42, 121, 1, 63, 63, 63, 117, 42, 42, 42, 42, 128, 174, 174, 172, 152, 100, 94, 20, 18, 39]) }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5756)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 4, 5, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 147 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5757)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 4, 5, 1, 6], ![2, 0, 3, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 166 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5758)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 4, 5, 2, 6], ![0, 5, 4, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 0, 5, 4, 1, 6], ![2, 0, 5, 3, 1, 6], ![2, 0, 4, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5759)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5632 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 5632 ≤ id.val) (hhigh : id.val < 5760) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5632)) = true := by
  let j : Fin 128 := ⟨id.val - 5632, by omega⟩
  have hsum : 5632 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5632 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard044
