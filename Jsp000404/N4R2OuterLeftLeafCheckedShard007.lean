import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard007
open N4R2OuterLeftReplay

-- Cycle fingerprint 00988dbc7eac616b6b514404a9f4df03bbce0fc47a03644466bc49c83bcea593.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint 012b9ffa2f694b10800abc233b2b0065137d695b58a595975dc814765443b13a.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 0176baecaff74ea6807f2af8f291185f6256fcf15ccfaed8a7547b6210e28e69.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 01d0d25c9a65b30ca34b756a8a7a155d965f3c652930760f56a70e7523d64a03.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint 029d60c7602805fca6913022706a0ace5f265d204a5c18cf258d36ff7f3acfaa.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 034203772c447a0753e7ec3a25be553dc1fb26ab60632806d729095e196ea304.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 040f8e479b9e3c87f2b7360ccb9d20d945aa00f8e73e36dd944fabd5fd09db53.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 04b081a9a96dd2ffd48d06047e693eb0947fc0539e571b88705b5ddc87ce6a6e.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 04e48b1159ee5accedab0d1f1d0ff521dd679b002263405f76eee831cfd0655f.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 05144428d8d666dab3e22de4af3c91728d46033ecbc47119b3ac4fb7b0313e8b.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 05929417c21a03fc76dc63ceb7f40d8bbd2b48d52da0aeb44fd9585059df0da8.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 05b40dfc4813fe69b3eabd2411a34b266c1cc0a7574533c6ba952b3f152bfaf0.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 06d574b631db2062d3888452313600f4bd91eb32115d34d9d245fa22008811b2.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1]
    constant := ![2, -1, 0, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 22 0, .triangle 34 2, .triangle 13 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0]

-- Cycle fingerprint 07239b41f502a2508c67a91d8103ee8bc8b0f3644a659d18c559adeb73b99703.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 075f973072869b3ce7269e95a9e51cd8a2973d0585d05eb18320f7b2c3c77be6.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 07617771145ba941a66f3b65e3c3a62ee8d0f4e4c24c3462f48e03a46cf9d84f.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 0bcacd6823cc6f46230c2e15799eb97a7c645102118113580c2651fc176be5d6.
def localCycle00016 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 0c5bcf40cfdaf18816254cd93c84b0cedfd8b9efe9502afda20a22cb5e7b7dc6.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 0c7c71d5c10e07cc971f3ab27ea5493f448a2df48c5d53b9c3e6fc7842639234.
def localCycle00018 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 22 1, .triangle 31 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 0ca00cdc1e381b5194ad0e7c80538aff3e5323d08d3dbd3362ca9b22f05e7586.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 24 2]

-- Cycle fingerprint 0ccecf61284b253e811696ffd5d5a9ba593b420a5d9b13a3870f0f5bf7ea584b.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 0cfe579feadfba5b25f9a2a6109f8de537e975cf00e9e9f17045c7b5af70dfb4.
def localCycle00021 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 0d998254cb6d5b175b65d3d7445e39a97cbe52759d68bdec0d55f91895ea0817.
def localCycle00022 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 22 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint 0e45493ef43cbda19f96b9ec7c590f5c837f2e6bc3b6c9da5d35728e5ece6119.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 0ec1416dd810a8d4148460c483469f9a15cbd1588d1abcaf191db0156a4b24f0.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 0fa673db412bd8c1232b97465001ffc745932f478f329b1118dd32e4a102a521.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 10be55b683ef2fae624b6cfa3e4e9f2f275cab58f883ed3d8f5561734602614a.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 1197ad0bd9f1826a2d607492f520336a88f1a5251ce4dbf9794e4202c25cd064.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 120507979a825079b3f940cdd42e5c7120f76327d63555ca0cad714990f76707.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 122a8b6b0420c5228fdaf2f64fa772ce6c404cbcb9600661b2c6932281a0c202.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 132d25a7b085e51256dd11cbebec49088b948a11c7ef59aa945ee9e15b7c4fed.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 139dab53ea9e44d919331bbc6ecf512b2358edefbafcae1b147f41932849a9a4.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 140ab5db5a6346a7f16db39ecb6c6f33541e7ab76bb40701cc888beeb79b2331.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 14b83cea571525354e826ac0b9dfecc42e6a20d045f32269823a65afd68df441.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 2]

-- Cycle fingerprint 17365a2cef5b5116b3757a7fa187cbabe5e1d05ac67ba7d026187f2ae2e28f31.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 17ceed8de7b44f004975b66118a91f5937a8fa4e701cc0070f9e7b68b9ef6d56.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 1942c6a0ec4272896e1ab88310d7bff299a29d8e2e735496b819080fe044bbbe.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 195801ab2b0a79c9fcd719e67580c9633925eacfa2b046c686042a78d999db7c.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 19d457879162f105a5ee4a43795bc6c95a8537303ff1b789f4fe97b22ba59274.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .gapLower 2 0]

-- Cycle fingerprint 1a236a503d4be24ce1c78d20d3eea8ab14780efb919167ef3ff5466af6419703.
def localCycle00039 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .triangle 23 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 1a558acb163975ad259048e9dcc18abc2e6bb57a9b92d7b10817125677557667.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 1b7c46c5c3b44417b6cbbe4fa628a19eaf9e71b3e1d3d17b512062bff941040f.
def localCycle00041 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 1cc5baa42d32a51123bef6d6be066a0ede97e36224bce823e07414b1d537056f.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1d195639e1908cc911e1f7c2e0442ff899228aa8ee5e90e0555d3cb33ed1622f.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1de8d98f2205ca0865def05058de5ae034d77b487df811faaf494e590b7ce422.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint 1e2da3e605511ee24289aeedcd0037e995397dbd9deb0de7ac8bbcad5966ba99.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1e5097d7f5232c6290a2083437aa870bf4d13d048f3441e1a380beaeb730215b.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 1e8886f718316875ba1fb5aa87cdb2cf33b695ee1e2bdd21348fa410427414b7.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![-2, 0, -1, 0, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0, .thetaNext 1, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint 1f423c05866faa64da7eda198c883484e6df0e972867abb538b8b351b113aae8.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 23 1, .triangle 19 1, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint 21001e32fdc49ed8aae07a1d43a486d6099d8662c4447998c263b8212046b080.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 2146336cd17f53755266706d047d4582dbc6e0565936641a790fa1c0d3ab9af6.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 21577032678b3b7507bf0725bb5e1f54e3a82509886f012c3fa32a5e9446f9a6.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint 21920a17c5e94ed5a23a25b11ab5384a66bf1075c6dedfc8c063a2af3b46649b.
def localCycle00052 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 4]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 4 3, .triangle 19 0, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 21a7274897f48b58e1eb5bf9f4a246256079094b11e6ecb1ced8993f8d177b1f.
def localCycle00053 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 22 0, .triangle 31 2, .gapUpper 3 4]

-- Cycle fingerprint 22404b30b56843c0c4dfac7cfae7a9bc13ffd9bcfcd80ca1bb12d9645ac74bc9.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 226d9f0a4b48fec9277d9ec102170239f895acd558d0ec55d29452db6d385a4e.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint 24ce62ad67e4616d8dbe2b0ef4f7aa120940d5170f3f7eaeffa65fa24ab81b3e.
def localCycle00056 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, 0, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 2, .gapLower 1 3, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 2501f4c35fed48f2a090285ee7e7806cfac829be9a9f8ef6b50601e033e9c743.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 263e5b76f0815a6297b41b526087fad9f074811cf92c22f4d4e3391e86b2a9cc.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2654d76553b36f5f18517180e7847a28fe8ef0d0c05a4583fe5ed1cfad619e7d.
def localCycle00059 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2679a1a8bee69d2610ff75551492b329e2141c8afd3d1849711868ac1646c1f3.
def localCycle00060 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2709d24a8e1c12fc362072acba18ad7c8a48731c96bbdfd4ae37eaf651fda87b.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint 273ce57af3e29b59ebe281d36d0569ec8d9d62aa98e564d4ef88c5b18eb7813f.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 28788793aacb7de68ce36618ee27ae2b95f73c6500659b2e83ac12273b5fd013.
def localCycle00063 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 4 2]

-- Cycle fingerprint 287bea02c8e599a9102104f050bdcce05756b09faf2462873d9678e49aed30be.
def localCycle00064 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 29057015d64b2bab694a6dd01e0e569c2a197b26775a96a8bb18a277247473ad.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 29634891d6e3fe04c6d66dddc4e94194fd01e4df9ef38debbe759f4f0bc779bf.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 2a7d1fb7384f10c9d58d1759af386bc7a8d53ca7aa307676cd3c0c194fffd2bd.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 20 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint 2b7c73f7548f1a1a902a93800a6bd8552e5e32142e64198b426646177da882dd.
def localCycle00068 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 18 2]

-- Cycle fingerprint 2bba018ac58cfb2ee53b5952f36d181ab53255f7e826efde886f8b73da4d996e.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 2]

-- Cycle fingerprint 2bce6387ae51baf26d1f4395ceddca69b39c9c3b254dfbcc3855bc4161b2933d.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint 2c29e77a64a9f92a7234ee1105076f556a10873520b2d7140f4144a55d828ae3.
def localCycle00071 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 2e271486661274e1a7c299405a1677a34c17366877ff18a8db97452392c64329.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 2fc2df1f680f9248312512eb7a4da43baadee90e68c34d86941243e2d3f0a2a8.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 5 6, .theta 5]
    constant := ![0, 0, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .corridorLower 5 6]

-- Cycle fingerprint 306083743dfa6967acdf8336328e2035744a23c4ff240f4c4a66b7b380be6dda.
def localCycle00074 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 30827bc3947f17c3d17646a37a1b957352b9f7285cfff92a979657f413931d41.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 316635142616d96bf9f835d726b1916630af83574c0ac20544f2b0e5cdd14f46.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 14 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint 328b347d031e74fd4f806662c1b096a667df60a53653bc9d511abcebf8999ae3.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 329003f79c053100348d69674c1da371af934bfe0fc74ce50fe11a0663591268.
def localCycle00078 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 330f50ac250701369fedcd689a701331cc1be3d3543e93ee768e2a1b57a20af6.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 33269564ce4201f717310950b9f0f36726ee96227190ed97c6e10336e9ff4da0.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 3344b7ccf28d9ea7a99c0ce15ee50a63d5bf8f5acdbe3b37315dd43902793d4e.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 33660f2e2f9ddde407bf4b22f83363d861149299d498457717cfe85572ca02f9.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3]

-- Cycle fingerprint 3479ba49f7595cb19a78d3f49470c11cd615d471c27682e441b333e0fb93ecf6.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 32 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1]

-- Cycle fingerprint 34d8c2c0c4b88f639b361c3b00a6b5e74cdcf04d45ece6a27a677c738e93efc4.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 3531274f58096a7eaef7255f22dbdc804fb10e9908b210773236416ce018ed97.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3686c051613df8f7819c3342c74bae231bbd9d30b8c9746f70c82f9b953c4e58.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 36976bb0ede86fca6c3f1aa033c0026a365902c33140fe6e0a2839c9b00344fe.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 3754687bb5fdc4a9fa8532989a0e914570cd5560c26689bbef74a7b71d01c729.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 385b00116db3d572c098ed1b5ba2fcc645463f1b585e81a309f1bf2eefe84961.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 38be005bd12af9214098044d092aa215fcaff419ceb200eae6f099268467133f.
def localCycle00090 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 22 0, .triangle 31 2, .gapUpper 3 4]

-- Cycle fingerprint 3a02e6f00d0e0ac495527c8b1f6872d3815dfa97b04dba497e5cb7ec47824e53.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .gapLower 1 2]

-- Cycle fingerprint 3c56874611400ca5cbc775f36e669b5927d5918548c7f130376d7f9c0d9e9d3c.
def localCycle00092 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, -2, 0, -1, 0, -1, 0, 0, 3, 0, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 4, .triangle 16 2, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2]

-- Cycle fingerprint 3c69647f8138deb8d0e712908df4f6631db751a49ee01e7659eb8ed9c55fb0eb.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 3c8b912bd885edb7ee80f40b990162e4e295db0de09fecb4fc59083ece91e01f.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 29 1]

-- Cycle fingerprint 3d50167d4a59cda3ed4fbabca3a14defca28463b1bd89515253e738ef7c09540.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 3e99fa27821518f4bfd773772aecfc63650af02df7a78c7ff132bc1e7b2c92e7.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 3 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 0, .triangle 10 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 4242f0c32e621a8022bf520efd336dcb0063ebfbecd3283f09a05db97c956177.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 431f0f152a995af9b5761718a21f9d740fa06b1e0a66f709c1997cdc59e0834f.
def localCycle00098 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00099 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 434b88f42fe7dbb4654797a17d589af325c67d217b4b2c43de7a6bb055a745e9.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 43ea03350251aa6ed34fe0aadba2df70daeb06de652353eb4b222563a45fef78.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 44344627e4416af664b389d4409565361807bccaa9737a18c25e1b49bdb3af23.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 16 0]

-- Cycle fingerprint 45f6993f66ecbcd2f7d7765d1d06b2104e947ab3b7e6e9f6e474498188d865ec.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 20 1, .triangle 19 0, .triangle 9 0]

-- Cycle fingerprint 46088c43c7fdbcf0853a55a2953b7433fe9ed9810fb65fde798849bcd04a5828.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4650bf0d1da9187d0f24bd0202ece0a94a48f9c1de41aac9ddb37c510c6898bc.
def localCycle00105 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -2, -1, -1, 0, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 46d1309cfe7c3446e8586c1bc8c745eb516923d056c17cd3068605d2346b518c.
def localCycle00106 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 47218f5bc1a2cfa4b9dae968c11b0cde86080d3c107f3d2d71fba472aa965a72.
def localCycle00107 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 3, .distance 3 5, .distance 5 6, .theta 5]
    constant := ![0, 0, 0, 0, 1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 20 0, .triangle 33 0, .corridorLower 5 6]

-- Cycle fingerprint 475f9ba84279d10d9a94b4badabfffbda0bbaaff20470710fed727071b1384c6.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .gapLower 1 0]

-- Cycle fingerprint 479a2a4240b54ba514f6e1f1832ba681a94e3b068cd9449c7f6ad2f536271a29.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 48231f6e96ee9b7534b50bf49ca52027e7b4914a18fc4117acd8104141a5aab8.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 48424aa43b3e80a07e234456e811e5b2bd0431c25f047086b1eb52e0dab78538.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint 48cb26c1e574bdacc6618f9fbeef48cf9523825f9a45966c74e78bd252554d01.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 49d76a1e53c4f47669f546791abf96f3661e74e2332e155a3789b69d8c161fe5.
def localCycle00113 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 4a8618a1c5195a2edc7a225050c3530e1c4f933607051f87a24eda9f2e3c8ae8.
def localCycle00114 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -3, 0, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 4a8b7511af9aed04ccb83c85a95afb0af95a89bcff6ddcc327159e7fc88395ef.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4a8eb83437153330bb00a598ceb08aae277fd802faddcbcd2b91d36ce36fbf5d.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, 0, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4, .triangle 2 2, .triangle 9 1, .gapLower 3 0]

-- Cycle fingerprint 4b34d5b65dc2c0ec0e26d19ae5117a9183a6cce87d528a56b643f788f28810bf.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4]
    constant := ![-1, 0, 0, 3, 0, 0, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false] }
  origin := ![.triangle 9 0, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0]

-- Cycle fingerprint 4bdf23a6b4fff21051dd0f21896f652b1d876f9a082268eb4d31f9aed7b35039.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4bedf2889bf7cbd56e723c7a7c613470b0ad6ddb88ba4fe0e5a080f0356c7340.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5]
    constant := ![0, 0, 0, 0, 1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 22 0, .triangle 34 0, .corridorLower 5 6]

-- Cycle fingerprint 4c6058c82ea836ff278833e6e9276ab2e22ed749ae23244c32ee23b2bea26f51.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4cdd7d2c2a664bb2e12fd93074b3d9ebfd6f2b1ecdc626317e4b1744d4262b95.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 16 0]

-- Cycle fingerprint 4dbae53827f60865e11418fb88123458f7f5f69312ca05a5ed236e0e1317ed4f.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 4e069421ca1f86a3e1ad47f7266a09a0be3aaec766e39492865dfdaa76488d94.
def localCycle00123 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 4ebfe5a9031dbed163e4f2f81d89c74a8282910dc3462faa806ddb9b41c96f33.
def localCycle00124 : Cycle where
  length := 5
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 31 2, .gapUpper 3 4, .triangle 19 2, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 4f3477b0e34706af0cf0dfce9db4b5c58c8bf58a2ed91b303cc3640a173297d4.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, 0, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 4f4331e0e94fa3bfdff9a620ffc967e2f5081bce54dba537d04c86bf1bd6c7a4.
def localCycle00126 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 4f82c5ec6e5edef96eebe505d6a6e3226e6519e53605c9d218b480070c6e8ff6.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 0, .triangle 16 0, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 4f8cf8ab17969fbf0cde9cdb1804bfc21b9e20a8d8b6516f6c3de0e3b9f81659.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 4ffd6e37edb57aa0eec9e961fe9241d68657d4fe083af9c9f5b128cfabb45033.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1, .triangle 16 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 5251ae0bbcd13b908d20bd5bba97db2c20bdaf8e6d4e523b9006f75d6994fd7b.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 53025ec84d13af688cacc24536731a8140acd17911f12c724efecadaa8b79a1c.
def localCycle00131 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 549c5eb3bbd385ecbe7be11f721cdd2e60da07b68f0bea7190b56d4ccd986314.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -2, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 21 1, .triangle 32 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint 5516b66a16e521fc46a45ae400827b4adf6a790cb9d965a53d3c5c6592f7ad9a.
def localCycle00133 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 55199540568bf387da71f81ce2d2ea5cafb95c18e6989014597b6ce7dc1735c2.
def localCycle00134 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 559d25a07e8fbccc1687f20d12bd3fd043cac38c882cf7d1235604f6d62123f6.
def localCycle00135 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 5667dcbedd7fb4acde5016f49a796aa3693d8396f3cb08810c6104b7c550f541.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 58c50c57194a9b7a5aeb3d6ed97ffcc74b1bcdfcf6615e1692bb5793804fe4e9.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5]
    constant := ![-3, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 4 2, .triangle 11 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 20 2]

-- Cycle fingerprint 58ea167ee6847aa7a2642a869da038cf44afe11882bf03c25f498f780ac81964.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5984d6fa43d19e033670444fa0564bf849ca4806eec6a880766877f1afc8465d.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 5bc94368459a44f0030d5c602d06f8f52142d51c9f1cc44122763406a5e0deb2.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 5c171c567be61c4b094ceb085d4f5d2e90f246ec48c6cae7b63bd1fbf8a4b00a.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 5dffe3bc07caf9d6c890e42ce767689e7d067e5b43794f0c23b0aa7662567b74.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0]

-- Cycle fingerprint 5e760f9e6662264d7c376dea3bfb881ac9f73b1a80bf375603649b0c20cf8a6b.
def localCycle00143 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00144 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 60171e38f13fa758a7244d9562a23afc62d2d11d7b20b97bc169161a8f1aa609.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 60517278de5c617e8f39f2cb0cd92afcf00e2c6f81673d6d59eeb81577577d25.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 60a13dfb08b673103fe413356b0e611ef6f8d2f94f7b984874afbbdb49c19c54.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 60c795158d42d7c14810f64c2c6813b23a55f1329cd4ce8ecd367977e2299ea4.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 615b7f364a52aa6346a34ae1b0d1cadb45ec73b5691dbb28d35b7c47628813b4.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 2, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 7 1, .gapLower 2 0]

-- Cycle fingerprint 619f5c922636350aff19be26fd258ab111c9266c6cf903609165ecca8218f95f.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6230d942593691bef280046360890cd1c7d369ea0b4e43fbc53264f94d3f49b2.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 62662e8c73ef22352267ea9c2b8077f949983084da2a6be6c6873506622c58c6.
def localCycle00152 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0]

-- Cycle fingerprint 628c4c0ad79eb7276ee7fa8c9204b90fc718a30f250462abd72fde8965939fc4.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 631906d683496afc13b99515f13840dda49ae2a363fc2de6ae003ac3efd61b54.
def localCycle00154 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 631f50b45c814eb6f865325842106f2a257e6867206d74dcaf9ce29d143f72ab.
def localCycle00155 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, 0, -3, -1, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 63446f4bcb0cbdd3ad0f65dc9bcd0be360895cded03dbf1cbeb30ac875a898bc.
def localCycle00156 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 63fad65c36bbbe445c6e17c8b1d6b01f64f647d7055aa75354ff50bdc1ca4f44.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -1, 0, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 6413f908e8d2c6d1dd33913fdddfa57736e43c69c6c8e6350b5c1a7cd83bb255.
def localCycle00158 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 21 1, .gapLower 1 1]

-- Cycle fingerprint 653b7aad068d56f91a568f7934d3f4c7cc1a412cf54466239062cf5dcaae46dc.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 1 4]

-- Cycle fingerprint 65c7d6b36c1a1cf4a8b037b3236a3d4796883753e3596895c308f134731bba10.
def localCycle00160 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .triangle 4 2, .triangle 14 1, .corridorLower 5 6]

-- Cycle fingerprint 6676a36c73d5564d94f61dc6e664a0b570919ced66feaee342fc536d30c3a0c0.
def localCycle00161 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 66b7a9d4b36684c40fb33488194a0e61bd3e1cd67ea40602f2ef784b4e692872.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 671f502bcf286a19931c6a655f026ff9142ea2cca180c491bab79186ca4a1844.
def localCycle00163 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 676ac0892a795940cd49ff2aa66fe5778a1a64826bc60ee5ceb908e513ad69c0.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 20 2, .gapLower 1 4, .triangle 23 1, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 67cdaec86441069a6a1d7e402136ddd7c523b8214acf7b63435c2e63dd427cd6.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 6871579ff589aa905bfed5fb22c930cbc3c6a67e17e4b92625d28778911d423e.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 68de44c4ca644f5e0d6d950180ff8b7a276b530cc0594e59617b5e5e278ac1df.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 6966293e8a11a6785ff0758160a9b78cb3dcddca905f1b02850d97acf99c3b90.
def localCycle00168 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 6, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 6, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 6cd3e78d7366b88bcf65149ee7126abc66888e336e6eef56f8127ededdd9282a.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 4 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 6d075645e78b09d1727b1fd05be3f8c985d5d94be8200383224ee30ebe0fb442.
def localCycle00170 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 6d8a06215767b570b32c70affb663f206a22f95bc57216ebb8b78505574cc9b0.
def localCycle00171 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .gapLower 2 0]

-- Cycle fingerprint 6e2ec19084a0f74a7df1750bd77737c6bd9dbd6074f33f5dc7fd6ead9def24a9.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 6ec2ce38305f05942b5c502802bc822a4776737067ab05b37337882b5a411d3b.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3]

-- Cycle fingerprint 6f243f30f11943a5c3d94c6f14a25b6249b30200ee08c1ebcce0761c381c784f.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 6f278d2af93e084f93eaa629dfe049f99fc8728d55cbf58e77dc1f4ffda9542a.
def localCycle00175 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 70af474136c64a2251232a516d4a77d46043787e503cda8cfd4355e7d969eec3.
def localCycle00176 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -2, -1, 0, -1, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 717899c9981747b0fe5f642a4280aed0261fe6a80bf7e119bbfe074fb3b9f34c.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, -1, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 71ea96193659485efc3c2cddaea6bad28a9bbe3fc41e7471fedc68847fdb0705.
def localCycle00178 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 2, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 736bcbc320e5f51a97e3a9d670c24e15979d7bd735e7eceeb2b2c415ac108d51.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 73ce53860a792d5a9a2b470928d6941a7506a190eee3c6d9e230062dd916fc78.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, 0, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 73f028b8165c84340ef330b85e66187ec19edfd7340563a62df9b3951c0b8fb5.
def localCycle00181 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 752379fafe9675a470b05178f11e750d0f4f9c43017c2adbbada13114d3aff56.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7587c057a35cdad7517e74cb4662d2cc78017f20be5da163c5468f20500ae6ac.
def localCycle00183 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 758b093560ad14dc2fbc18de69cc88cede70996cca66754dfc6730ec8679530e.
def localCycle00184 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 75b7cd0080cac80e88a9cebe30b1ab38cdaa67003f15a02e75866d7f9ff0bc37.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 75c0e8b1c6c25c2b879fc73fdc40f06631e138700ab1df1185c35d98f3b8f8dd.
def localCycle00186 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 774daed540c3dd393e8c878703781cb94dbbd5063b2a9ef39f9eeccf3e77ef5a.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 21 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 78602a9deeb7032317240f917a59b818370aaa1eafa286bcc8ea0e6f7fd215a4.
def localCycle00188 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, 0, -2, 0, -1, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 32 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 78771434bd30b2ee7159f616d3dcb16531d38a988cd29a3230e9bf9148be9567.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 78a22de08a9d92baaab88d3e5ed0e9f1da0ef7cc76f7cc234f00c2a5e6dcaa10.
def localCycle00190 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 7abb8601372cbd27120d00109b76c25383976fe087ee09257fd962bd144dd5a0.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .triangle 16 2]

-- Cycle fingerprint 7ac11edabceb51a6882dceb6d36755c7fc16f99cde664db324ec6a484759bc18.
def localCycle00192 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 7b4ca5bfd400ec5d2cb4bb47ef69bda91471a6a28723e51227c8124846e654ba.
def localCycle00193 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 7c4d14846d041d455eaf4ba04e7f810d28aa85ed91c2eeeb7ea7b854a12c7f25.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 7d2e41231421f840d9e4f10c140f13605ad72aaae54c16965ace81912fa4362a.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 7e3936559cc58da83f461b3ac017e8e3ecae610a66a0da91b29703f7598e0ce9.
def localCycle00196 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 23 1, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7f71a21734afcf5308d4646abb219f7d5c8e9bc7d3081faac1967eb7563c3cbe.
def localCycle00197 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 7fa07494ac197971d658b7c4b2855b93c4613db5e7da9be7897dec323f148c85.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 80888152f3b6be393c6fe20129525f4d754608fa6b24533692cde1d2ab61a50e.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 80c054f41a5aab00d08d0f06849060b558b82ea9c5985f4a06536de154c77995.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8220cdb75d80f0b23ea158b7950ab277ecbd4d81a7fd69b8454cef3eadb037cc.
def localCycle00201 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 822ddac943a5b952ba8e89f8d826b346b48fb5a0f82835b3ad788bc0f145b9e8.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 824b53c2d9c052377011f27fbd93c9e2612ced050b61ffdd780b6cec73fc77c5.
def localCycle00203 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .distance 2 4, .distance 1 4]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 2 2, .triangle 16 2]

-- Cycle fingerprint 82be5e13e5a977f4d67abef83066370c2e7f1a10733a3916755b6ea8dea421af.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 82c356938f38be75652a4625c1c373b80efafcacd6ea871422597613875e5ae4.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 82defdc70a19f7c8ac0bd498b9421858911c79de443412852bc94b3cbe7ee983.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 83d25514645b1a16d4ee85d37c43293f2b546fa833a886a9849077e3195a9980.
def localCycle00207 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 84273045f7d124f22f686249ff73cef55bd1de4da98900feeb7e5afff25d62fb.
def localCycle00208 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 847c4d606fdd3739d29c43630bea2af14950220796265ccc3388b5bdd355992a.
def localCycle00209 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 85486d0474bd8c9160f8d62cd08dd5c5dfd02b62f661862560eb6f34d5a76f72.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 86dbe340c6b6ae3b3540d6bb4e8ec0e3ffbf68d9543585a0df91fd214d579520.
def localCycle00211 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0]

-- Cycle fingerprint 87f84aa310e6a83c946e63f6ebdb2334f44303567cd611b27d0f31bd70e5aa62.
def localCycle00212 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 87fef2394ef7e346ce3914d5f89a0e0d753903e8b4207c9cbf838b337925e38b.
def localCycle00213 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8826069bc41f788bffc10f25ee2bbac7a002fdf2028fea2fabf7d4885c64dbf8.
def localCycle00214 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 887a48e65db2e281349c6b209cc4c6078692857d4a92ea80775004063c940a4c.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 88824eb050533e276747f73f89f961a7c63a52789bf6f26f5fcaa3b71546cde6.
def localCycle00216 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 89a4f7806659950af4d6c7f31b58c229499a5b6b53df5e161b335f956b2fbe10.
def localCycle00217 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 89ddd2648b082aee0811d4e0180242fc5d30f80628d513d16c936bfc67d55153.
def localCycle00218 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8a4654c2e8cf5a195eafe7821b0de879fbda65e15d8f2abae62f975e347606ee.
def localCycle00219 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8aaa6095975f36095b3de42713356003a791a260090f966c2f5299ef17c6f22f.
def localCycle00220 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 8ab759b426a3e7803bfaada12603ffdeb6210275a12e69a3f9eb0771bb4ba9d1.
def localCycle00221 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 8ac878d008cdfa0e5058ec4cc84283995da2edd92b8f8d5d77a4a518873eaa93.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 8ba612f31cd0c565af622b85d0b5338a219aafaceda0a7c981cfee2f289c6823.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 0, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 9 0, .gapLower 0 2, .gapLower 2 0, .thetaNext 1, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 0]

-- Cycle fingerprint 8bbb0043189a8a353bbb1cfc51e69f68c9cd1e0cfd040bb7c3240609792454dd.
def localCycle00224 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 8c97446fbf6816699186a1a135ccddae118488799168def45401b2caa20a77bf.
def localCycle00225 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 8d1db3f8cb1e725614c432d574ab0e7cbbc13aff64d1ccc74db7ee22f09d9c3c.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 8dafbd75e9b597686478f5bfba78e6ac5e70f3c613bf70dead1b690a3c21b6cf.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 8f9783c7c2c89e013df3b5e1fbc3ce3871267f7a661b9a9298dde2a677aa62fe.
def localCycle00228 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 8ff0c869e7f13daa9dde43c93ba16b9a5d67308f0fdcb562f74bd0816fcb4dc4.
def localCycle00229 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9114dcf2ba44e3c43bbd85c4046dbc94b32969c6477fa8426ddd2dcfd584af4a.
def localCycle00230 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 9168961527df126c219b37eb540464e4c243a958cf00dae3df67d6c16f27b334.
def localCycle00231 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0]

-- Cycle fingerprint 9299395381ad03266d21436831ce123948d82eba42fc8bc40cf4eecbd340d23b.
def localCycle00232 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 93969f84a1947e986c7e84359200430c2dbec1973a2394d9c454c3f9704ef4d7.
def localCycle00233 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 939a9f65243e155640b536c64534b5936ba0d858afbe1ffc83afe3a937c98776.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 93afe1df27f763bd780b8b6c5580f2b6abb2fbfa9b3d08b162856047a924fccd.
def localCycle00235 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 94325c6fc08a66f0784f0018e6b74a842186ff5b7d9cab02ea620812cd621a69.
def localCycle00236 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 94b03597870a7fd1a18ee63700dd9626f063037e4eaf9471a24b3fd4e27bae9b.
def localCycle00237 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 95c1caf100df4d65016a487ae5857a571c9fe144f9ba131682d46cc3cdd3d270.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 963a9132b868d86f480e7694090b52b5c510aaaaf23a1a6cab0a96a430bbbdef.
def localCycle00239 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 31 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0]

-- Cycle fingerprint 973f6d567d1135534acc13122e39fc4e2ec7a818389483a5accb50657177f304.
def localCycle00240 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 9841e077748b26eecef003bce1c9506e54a3d0facd36a4f8e16b5cd72a3881c8.
def localCycle00241 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .triangle 18 0, .triangle 27 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00242 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 9885c7d177f1c905965b89dcdd4f8dc0d82e8c1dd73bcc4476b39ac30e5d97c1.
def localCycle00243 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 98cdaeebdb6ff6b0dbfb0097769dae225af628f414869568d6de022d3c51c7cc.
def localCycle00244 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 99ad453d6e27f33cb1316f73d871b307dc573e79a3fad75d581fc3dc8de305be.
def localCycle00245 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 99bb15ef2ecaaff7f11e0b452a2905c69964907899e6de06ad602041e152bcd5.
def localCycle00246 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 9a5934a5ddad474ee54568a6e30100a56bf779c86a0f7b487a82aeb82011fd04.
def localCycle00247 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 24 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint 9ab97debb8933da9eee8498c85e61b46c7fc1fc2632c5cc7dc8b6ded9377c73d.
def localCycle00248 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 9b0e4df5326e2e94ae2f45271c626ec9097655c30ef0906249abea3f4c954131.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 20 1, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 9b68899fd6d83e1a8a3aa51a7cbf28c6f1e8fcab1f05cfaae04ab5d6aae87b59.
def localCycle00250 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 9b828e6cab49028ce84e20f9369d7465fa98b665f9226d466b11a8d0e41cf76b.
def localCycle00251 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -2, 0, 2, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, -1, 0, 1, 0]
    strict := ![true, false, false, true, true, true, true, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 2, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2]

-- Cycle fingerprint 9d9d5275f41fcbb258b6beb220cb6dd02fb7ed97d710971c51217271d363278d.
def localCycle00252 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 23 1, .triangle 19 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 9eb4a2f2e6d4834a3079ac7da1e59d5b88cf96bb81068d4000b943e3474073de.
def localCycle00253 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, -1, 0, -1, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9ec9edefce5d0e5776fb67a58a44bbd3659805088d26cfeee62fcae21c52c178.
def localCycle00254 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9f32dad70f5ddb30ddbf1899325894ed660893141b19ae34867d27274a5171e1.
def localCycle00255 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4]
    constant := ![-1, 0, 0, -2, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 0]

-- Cycle fingerprint 9f763a901518418d7c72d035d5cfbe30b8482cb2146451fae1b071279f8c85ba.
def localCycle00256 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 9f8bb162b6466a2154dac232a716e797a792003ac3882cb57afebddccdb08f89.
def localCycle00257 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 4 3, .gapLower 4 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 9feebb43494aed73ead45c913020fd3fc30b7148bb96999054937859ca28370a.
def localCycle00258 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint a00c14c9538a435cce2fd9358a38550bc8f7422e4c81a53501f93833da32ecc9.
def localCycle00259 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint a0bdd37a5f596ea9fd92bcb1dc414d81e9df06cf59011773b03bffe6fc740bdb.
def localCycle00260 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a17b97e6522872fcd9e25411dcc9481ac452efd3d11cd48ca3581a5e10557ab5.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a1e82bdf8b2be7b8f35a93ced9e33a2efa967965c34fdbafab56953c0a6eba6d.
def localCycle00262 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a3bf77dea82d8e2ca4b8a04950bd65e5470e10c1d5dbebc41bf3f24fef89f1f4.
def localCycle00263 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint a5ebfd2850fc1da1a6c059ac537fcdfd6724b3aaccb3e362571d91c80a3f7802.
def localCycle00264 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .gapLower 1 3, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint a5f7fd127afa6c3b5239ffdc471d9888c81aa6eaed86cf928b8062361aa3d729.
def localCycle00265 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 5, .distance 1 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 20 1, .triangle 21 0, .triangle 32 1]

-- Cycle fingerprint a6ac85c8dad49f65169960ac8cea837a4d7ac4a3cc08a1e2b9a1518e30a39cbb.
def localCycle00266 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a74fbb609bb4fdab47f44b1a369af62a9bf97d9e8f48224b0a9190ccb22fb352.
def localCycle00267 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint a774a57eae688c8a66c2c167e1b33ad56088c5b3e6b4805e9d51bf24475334cb.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint a7927311efcd0e95fa826ba09d48ec0c7ff06f2d497d31cc224ce55002931d87.
def localCycle00269 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint a845def362c73029eac705a408445e24060c1b43368c1a2e245a80b1777247d1.
def localCycle00270 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint a8463b2d29969a70e14573da7f83075cdc921c1f391b1207023456aa7a3e086e.
def localCycle00271 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint a973d1ce0891db1eb992ecd717d0dea7cad8a2bb6a3fc4678aa09f2bb1afe715.
def localCycle00272 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint a9a1c5ef5da821188b017cf6379f82c1e15c339d2efa456de006f53832a95a8f.
def localCycle00273 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint aa3c93efab8c7a785401775c53e9d271441ab1c196347f3be43e570f5c8565f3.
def localCycle00274 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint aa4a452e9eaf48fe38cc3be83c6b47c3aac3555e37a1a9b1e4963c4150bda360.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .gapLower 2 3, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint aabe3e1cca54ba899d9e1ece80ee15af8a4d7b1d6b54bc212fde0eea9b3ed89d.
def localCycle00276 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint abf40c231646ed63e816a039da6d845c9c0df09069f15bc80fbb1c706fd7de96.
def localCycle00277 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint ac387c781c9641cbef298220dfc3a640a68b40eddc3127bdb94accb8d1782a4c.
def localCycle00278 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint acbad68fabae1f357106d60cf43314335b5eedc7409d7712c7a54ed3db5061c4.
def localCycle00279 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint add0069579fd2bf18970a186a84b856219c6795f92ea2428f9694c346fd051b9.
def localCycle00280 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, 0, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint ae03400d038ce89283af157eb40fa04ebc752c87cebd83d249b2355ed2a06c1c.
def localCycle00281 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint ae9275507efd631f9e98e7aedcd3d02787f2d04fed7ad339cd8e19b87b313f7c.
def localCycle00282 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b06bb9431357fe133d320be6f1afcb3803c9155d5fdebfcc689aff58c24542a3.
def localCycle00283 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![-1, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2]

-- Cycle fingerprint b0d1cbbe5c63833ab41c165222a2390d5799b9a7861f7ec6f4fdd6d662705a78.
def localCycle00284 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint b15b72f8189075089648677e021057b43a8e75bb6484be7d3ba2b7b4337bd8a7.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint b2a998eec82878d3680c0e7de304fd1d32956223c61d8fa3b3ba0c9167fbd043.
def localCycle00286 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .triangle 16 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint b31843cd0d4223406b3ea6e191706461a5511f26371df9d03e70a9e9d3b05a09.
def localCycle00287 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint b38f819ac6e8037d268f21d97ea79112e3de0576ac967d3a8d29501408ea6c07.
def localCycle00288 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4]
    constant := ![-1, 0, -1, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2]

-- Cycle fingerprint b3d41b171d64f688404ec3728ddc23f8ae2aaeee215eca1d0b73ad1be07eaafc.
def localCycle00289 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint b4778a4083686d45e0365faf3d655652be257f5e8147306429f05f96b516e3b2.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint b57257c749df6f95d8bf332f60b6429d4fee91fd801e0d222685b5b8b78242a0.
def localCycle00291 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b5b646243293e66f56ba5831b715de236e89fe912104231fe1a3498351a65604.
def localCycle00292 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 16 1]

-- Cycle fingerprint b6032f41459296019b6cc8681df68cfe3004ff762324a537c798ba67b0b5282f.
def localCycle00293 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b76e15cdbe434c257b9a2a8fdb50cff7ef39daf48721e46305902c40fe303364.
def localCycle00294 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint b7d282b64a072da4b70cd21ed173fe2619736547671aa0edb1b77ef4e24f106d.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 4, .distance 3 4]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 18 1, .triangle 16 0, .triangle 25 1]

-- Cycle fingerprint b8296f4a92f26d39c2642531ec87fd57aeac8d27efed0c515f39e7f005421622.
def localCycle00296 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, -1, 0, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint b94351ae4a8257e7a5d263f5af79040167e9469530fc5b52fea3eca95a357053.
def localCycle00297 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00298 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint ba9d6aff4f5eed5cfd2750abf068b25dc96a4d28b854e0654eaa73459d7562fe.
def localCycle00299 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 2, .triangle 22 0, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint bb474025541cf4e41b3db8f6aa5bcae70991943d84e0594919d67bfc3416dca5.
def localCycle00300 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .triangle 21 1, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint bb67d5e77bda9a9db8d20c5eec1bf88c05178efdebf640a23dd0fddba2b58982.
def localCycle00301 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint bb687b44b7bb2c6871f7411fdbc5efd2f3773379af9fcca61f4dfa05f28a0ba5.
def localCycle00302 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3]
    constant := ![0, 2, -2, -1, 0, 0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapUpper 2 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 9 0]

-- Cycle fingerprint bbf9482ed71eac3009dd4345d1df3635f530d366b10181da4243aab55327c70e.
def localCycle00303 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint bc9560c0663aa448eaefc7fba8ccc6db34390374a98a15733497f8e360e5100e.
def localCycle00304 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5]
    constant := ![0, 0, 0, 0, 2, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 22 0, .triangle 34 0, .corridorLower 5 6]

-- Cycle fingerprint bd4eccf4435dc0468d5e04b5a618ed5bc55ff8ecd9bd4b8a1d27107106e3d981.
def localCycle00305 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint bd59dbf5af3548c7ddc92b50f9e73b12d04342cf4846ecd074cd02469a9a92ce.
def localCycle00306 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint bd5b1e6fd88eca1946b4da0f8452dc818f1f341ed4632e5f1f40e12df2d04b11.
def localCycle00307 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 1, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint bedb7b72619196d5aa5287b289d8ceeeae841a29b7a8c737d8717cc822f60790.
def localCycle00308 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint bf3bee06dfa54e0c97e0645c80a7bd04574d4d598beb115ae1b889c83b3b3d07.
def localCycle00309 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint bfbfdf4ad55a4b75c2c1974e9abb473c29c33e2974e0755b9b148edb0e660b74.
def localCycle00310 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 4 3, .triangle 19 0]

-- Cycle fingerprint c00388e76c51f92b117d46109bc7a0f260f32b291fc71343e52b826915f0b1b0.
def localCycle00311 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c084f99495a894972d2780cdc7287758a8134740f34a1276a1d25f1761b1bccb.
def localCycle00312 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 21 2, .triangle 23 1, .triangle 13 2, .triangle 14 1, .corridorLower 5 6]

-- Cycle fingerprint c17ae11c10af6263998b706a0618eb3e488f6c53ebe68a353a5c7c8285f3ee85.
def localCycle00313 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c205b1c7678706edd3b8a7f70f883c4234b5d3a0cd22a231355d22293023726a.
def localCycle00314 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint c2a390897630d9d927a62b8f0e51488ba6bd050484cb9a8118d4945ac97c4746.
def localCycle00315 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint c4edb52769a32006299f180b90f4abd6f72662c3573d0e756c67e2d4305637af.
def localCycle00316 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint c50e49b3cc249a779daa61e5de1452cc59375bd7d0a37525b6348a199df43b89.
def localCycle00317 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c59b2ae221131ca1c0fa787476e152d6e1b6b6c46409865dae1374feab273c13.
def localCycle00318 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint c646ce5fd3426db9ea3b3df395591d9399da259969b18cdf26d0e8c620d6fad1.
def localCycle00319 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c79732f4317e7bf2504e441f1234944da57fb63a4c3e243f5a339a75616c0945.
def localCycle00320 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapUpper 2 2, .gapLower 6 5]

-- Cycle fingerprint c87299e92e7d274730626fdc2d62a2c64d0db1c67585a0352a1815798408170e.
def localCycle00321 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c986a308d5f430a49a9f823e70e271477051a2f0473778c4737afc4b1ea96277.
def localCycle00322 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c9ddc208af3c5cfaa34c1b57aed353545b3e3d2a54e95c433406963aa93dc07f.
def localCycle00323 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint ca3fba20fb27df6a8091d77b32c7dd82941d7a8ddfd78c0a9ff730d9fd05a823.
def localCycle00324 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint ca4885f03d6afe438926a7393ac939d90de0891b092f7108872cf14002950f84.
def localCycle00325 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cb2c3d2101b2eca91d60881653aee079c8eee92326f4d7c6f6acbe2126a55717.
def localCycle00326 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint ccc1f92ed4ad6c8265a091e6047b2ed19c84332a45068e4ab34ef3197d6152c7.
def localCycle00327 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 3, .distance 3 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 20 0, .triangle 10 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint cdc558b4a13fdd35178ff50b92da4d0bd92c218bbf040f6fb4bfed972b54ed1c.
def localCycle00328 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint ce7eac70bacb67eec2af6111238ac1c29f8eaabcd027f39a29ac7ed39c135144.
def localCycle00329 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint cee50b3b5d45df0a57dd3ccf230cc24103c81807195828873a9ce7ef2e7da345.
def localCycle00330 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .gapLower 1 2]

-- Cycle fingerprint cf4a08bab08f37ffbff13133fc8fad22f9d0ea4d027f25aaa2958bccec979c2e.
def localCycle00331 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cf65d6d7fa3c39c6e36c1982081ffe25f80ccf85a072fd258218c1a05e90c956.
def localCycle00332 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint cfd7bd87ecaad83f86e3c9090da6b52f28ba53daa43261ba10338460cc7aa4c4.
def localCycle00333 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint cfecccb6d608ea72082d4cba74cefdfd0415c2c36bc6aefea6c9308cc01439ce.
def localCycle00334 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .triangle 31 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint d04b40f4311af150bc85fdc5cde9533edc21f83d0ce46b1facdd4a22e4d38c3b.
def localCycle00335 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint d0fe58d88d92016314b1424c6d7806fbc2e3c8f16862550197f80a9577336431.
def localCycle00336 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d120db563c8ccebde67ccf0f9b340cef81e0f3b25124db9bcd79fb89fe4e0f11.
def localCycle00337 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint d2666dd4ec83606a6ebf73546899001b855d82824db28ddd89b0028731656922.
def localCycle00338 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d2811ebc7d60e68a50a10fcba2f36aba9b20d5cf3d8c8b2d23953d964ed98b1f.
def localCycle00339 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d2ae7ba9b32715403d765aababc6bec6067e41e71c3b87a240d4ba577ad29f04.
def localCycle00340 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 4, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d2bbdf37239167176b9793735551687b887063d0e03d122655f51e1772e2f532.
def localCycle00341 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint d4a0e4ca89b9dd1dd0d537294ea9d2d10fe9eaa7bd9574e505f234665e159d43.
def localCycle00342 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0]

-- Cycle fingerprint d5a989a0aed197970196e7b3990b5da169a3ddb817203fc6c619d7b1994d1f3a.
def localCycle00343 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint d745834d3dd17a8cdc1f97b260c8cde7e7153e1cca86bbb8d622c104bb683d41.
def localCycle00344 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint d7d1a3d76ebaeae05fef6f78fa8d581a5f7af4df894006593577cb1d5b9a1c15.
def localCycle00345 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 4, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 5, .triangle 4 2, .triangle 13 1, .gapLower 4 0]

-- Cycle fingerprint d967b4869fecf9f6845802ad4100552f22e5638beab30f14a95435dbf29eb6fa.
def localCycle00346 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint d9f3be1278dd198fa3f39549baa07e2f2da177d4debbabbf8edf17039c555ed9.
def localCycle00347 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint da065135bdd6b0066b7a886eb280474fa8c4b15d1fd787bc5b1cf3afb60fec1c.
def localCycle00348 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint db18484c8fffe4ba573419e0e735c11c24b409ad80ce01d435914f4db17f0c3f.
def localCycle00349 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0]

-- Cycle fingerprint dbe105d62e9f57078e9b5dff5ec4a34935da3700703b5e4d342425adfded4992.
def localCycle00350 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint dbfdfb5c5828e726d748542b2c5ad38eb6df0021ffb46f09f2dd9adadc89a32e.
def localCycle00351 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint dc21b5a65f3233f74bb487abc3a1d0988134dc049227311a7a464bf7f5119d56.
def localCycle00352 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint dc46fca43f2b24c613c73ae3033f2fe5d468857935b12a42ede5c0a5344601ec.
def localCycle00353 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![0, -2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 19 0]

-- Cycle fingerprint dc5b9b739223e58a342c7d7bf5acb4954f2aa6dcc1b40df9251af52e9c1a7e58.
def localCycle00354 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint dcdeddc9b723949506e5067a04405802c906d6523fff4319827150452a9ae32f.
def localCycle00355 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 2, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 7 1, .gapLower 2 0]

-- Cycle fingerprint dd3a3a7bde32779e6ee6a5de1188bec81c8ec0f01bc26ca6165cca191da12a0c.
def localCycle00356 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint de02403d8fbfc80e01f7e776e0a32c219176b85d5bb6fff8e5f42564ce1b07b7.
def localCycle00357 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 1 4, .triangle 19 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint df2dfd883d8a3d7cc9d7a10e0a882b30c01a082ddac6280c0be4585de4a03048.
def localCycle00358 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint df53880c34aa5dd639a380b15f057b9bf3cd30b160d0ec365dbfe5069620c122.
def localCycle00359 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -3, 0, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .triangle 15 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint dfd318b9403c8af76a6777391919d6cf464e00df578d1ecf63e4020ac7cd6437.
def localCycle00360 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e10f286ac04c10b35271e38e177909873369e47244aa0e02d2b9d82089b7a992.
def localCycle00361 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint e1212cba1de0320fd65a6ed62a1bea073ff44624fd3b3b922be11412c8146a45.
def localCycle00362 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00363 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e22763b22e15d15084ab0d1cd4b585974ca137c2e78d0a0deeea7f47f294da2a.
def localCycle00364 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 18 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint e2f0c0bc885d472ea20f68d8abdc52078dc2bcb93b6b56629f8f4a82cdf0480a.
def localCycle00365 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3]

-- Cycle fingerprint e30bbf6e26d7fe95291cfe94ea0f7700bc3b18654e38ed415f5ff70ccdfebb8c.
def localCycle00366 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e31cd20ac8a54d1eefce3219478e06ab846a5ba96bb6fcda5299633ee15eca88.
def localCycle00367 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint e3b8bdefc3e6b35b00bc93f2cc5b492776dfdea9b682178a0fa6923ed883b6e3.
def localCycle00368 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, -1, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 15 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 25 1]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00369 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e5e95cf4bb708fdc1898b9018206ad0459a5466a1454d6902bc1d722596d614f.
def localCycle00370 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0]

-- Cycle fingerprint e6268d33e362e5af2177659b0aa23bcd55f15f7e34e35e0dbdd51dfaf38b0087.
def localCycle00371 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e678b95afded36f5e849ab16311035e8ca5ce14acd056dc3b4086b66b6dfbed8.
def localCycle00372 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e6b9178c4d91ed867147a8ad020f4557ecaa7617657001609a52b97628d9079c.
def localCycle00373 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 2, .triangle 4 2, .triangle 14 1, .corridorLower 5 6]

-- Cycle fingerprint e6bbc3e30e7cab6e1a6e6715f2a9b413e05bb0cd2d4f76910820ad7cbdd18f1e.
def localCycle00374 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e7a434a761c34e80e81a640e90e83c6b58c05ceb7bff28741c1ac8a3de4f68e4.
def localCycle00375 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e7bbf0ca567083c7971af3ae49b5655de6e5792bf0cd032c9dc31503152129f7.
def localCycle00376 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint e828903d6c7060c8c6444c2541408fedb0f7acbda7eb526ff5da503cb6beae21.
def localCycle00377 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .triangle 0 0]

-- Cycle fingerprint e841e3efb2ae5eb1b8ee122ef6b051ffc4afbc2be739fef15a6d8fc8e2c67913.
def localCycle00378 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .distance 1 3, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 2]

-- Cycle fingerprint e8503f7e7c0cd6ecf0e9078ff78d8d6dd1725307335569baee8e66ea43d67cce.
def localCycle00379 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 6, .distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, -1, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 29 1, .corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e87f0de43ae23f7328acb6598cd1c1364952af1042353e5df82f8a5eb18ed5b8.
def localCycle00380 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e93f3c30fb3b3c1d3380e9b232515382d96e28b0eb98876e7d7281eb25ec0482.
def localCycle00381 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 23 1, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e988d55943747bbab3fb25a36c27c82a288a10cf05422b2682cfcd771d954d7d.
def localCycle00382 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ea465190b3de5114e2afbc87cae3b5773bfc603e2689a593fd66c480d72a8f09.
def localCycle00383 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint ea57cd2d52dde75aebb7f35c57f86dc96e43fed5d5687e4d2929db130f2d7be4.
def localCycle00384 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint eac40286db67525356d052a6c8de2ad24c6edb740d52c9b3b683c466ce253f2b.
def localCycle00385 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint eaf55b498e55c314791361eef4e4bb8276742e197d39314c5234b692635e3977.
def localCycle00386 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint edbe47c92e8318715c1c1359ab0477423e4a27651a9faf442d0b87ef10f58b2e.
def localCycle00387 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 3 4]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 32 0]

-- Cycle fingerprint edd183f4d51f91d67ee616be57b90c7b034a602ccaecf2bc5957282dacc98a62.
def localCycle00388 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint edf8e68e7be57aa95717b51805d083b40f0193c91fefe6a8ea7cb8b89687cfb1.
def localCycle00389 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint eec9567d242dd2f42c82db86475257d3b050d1984e2364d3de40ad581f1b1b3d.
def localCycle00390 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint ef39048ca1741f5cd02ecd1136de192a76bb280163d6344ecac97221a40a6d96.
def localCycle00391 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 5, .distance 1 2]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint f0521cbfc10c52e81c0844c917259e3b0c74f93d0ef5517207a7c29e98caf805.
def localCycle00392 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 3, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint f0e3bbe206cee15c7119f051cb58eb4b46bf86eb7740a08a14b46f1d530c6100.
def localCycle00393 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f150b1fc1433ae759aae0332701eabecfcbc83a841a621cd4b309559c2429bd6.
def localCycle00394 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f254724245ec743c9632f872bc524e090e32f2b0e903900d97027299c023feb3.
def localCycle00395 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f2b783cd873dd472f64b6ae83474b525fd2d76dcde37f8e5569ddd031eb78e52.
def localCycle00396 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, -1, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint f309dd6c6c266fb055c208b2f5d0d23bf3c3aa313dd07ae7d5ef4bbd4f7b2129.
def localCycle00397 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 2 2, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint f35b45b87e24f0a7d84682a9c28019aa997214d76b64fe05898bd8b0897cc1bf.
def localCycle00398 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint f3a958f471d509b485616aee42d21671ce8b36515e3abf8423566b1a454e0d01.
def localCycle00399 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2]
    constant := ![-1, 0, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1]

-- Cycle fingerprint f3d921d5b3a690eec533d804ecc77a599b969204ca4d528e1a23b015c9abd094.
def localCycle00400 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5]
    constant := ![-2, 0, -1, -1, 0, 0, -2, 0, 0, 0, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, false, true, true, true] }
  origin := ![.gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2]

-- Cycle fingerprint f40b9cb3ebf655ac278de1bb22132eaedff1ceed224c93fe1390397c8285d03f.
def localCycle00401 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f44c7f6aacb9d052dce7eee8b5c080e8babb66fd59748fa5ba29c5c7877d1c54.
def localCycle00402 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f4773fc25ee25c45d12fdaf4771f45ccc72e155f0324cf8547a7db408e765521.
def localCycle00403 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint f4d4f2bd49a24d1675d8a762bdb8d132d16550bc5dd8a84dc9d70cff0ec01a31.
def localCycle00404 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint f57b8786c03050636f005861a322700f372e90384f43170cadd41edcef4e9cf2.
def localCycle00405 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f5be78a0e83cdfd2bb72dee0da714939b9cb5913b9f7e710c74e935b2a13e4b6.
def localCycle00406 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint f5d49a280817d08db13e784f24359c90431e6d34c359200854c33e3485bdc64c.
def localCycle00407 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint f63fbc0a1f960eaef5e9e3c144a8d55b93cae1bb030c743e816ebacc28d51cf1.
def localCycle00408 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 5, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 17 1, .triangle 16 0, .triangle 25 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint f865562efad7d922ac5a9569825d6b9ea0db14ae02914cb0fb410bb4024a7520.
def localCycle00409 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .gapLower 5 4, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00410 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint f957a9fc9e5b9b57af3277913bc85499b94951f82241a56bc773b1b6e7686aae.
def localCycle00411 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 17 1, .triangle 16 0, .triangle 25 1, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fab6f2b1adf7d422f8f1343cf79cd5f170c0f3e2d0e0bd5402f7c075189dfc1c.
def localCycle00412 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Cycle fingerprint fb2642c7fb7ee8ad5c8965c1478fe20e8d31d226bf7d5dc44f240f5f4cd35f64.
def localCycle00413 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fcab0b37e5a31e453f05a695b900baba2660f4985283ab780b86f99dda04d57f.
def localCycle00414 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint fd76da20dbb10c6148d863f1a665f68139f2e8f186815a75a3047a89d02d6b71.
def localCycle00415 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 1 4, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fddd90d4596465193b06ee2dd1b41d281c11462154ddc1ed0f77d65a09f5ef11.
def localCycle00416 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4]

-- Cycle fingerprint fe35d5e8fdad8bd881cd256d1c7041fbcdb9e45c54477225001fbe2d8ca62fb0.
def localCycle00417 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 21 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint fe5f31d128574398a3b0e75657c6ecca61f2515987350de9e1dc8c4ac2cc485f.
def localCycle00418 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint fe768191324e06bc6742d2f68c5fc06acbc3a2b2e8d38e1b83eed2c8e96ea33f.
def localCycle00419 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint fef5c9e8d1adad2d29c8b4065e9b3a5cf1384fc8f8da6da77044058e743ba8a3.
def localCycle00420 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 16 2]

-- Cycle fingerprint fffdd3e75b4db03781bce2b949b1f79d382a4c0c3a157c2611c6a00e0cedd7b5.
def localCycle00421 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

def library : Library := fun id => if id < 211 then (if id < 105 then (if id < 52 then (if id < 26 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 19 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))) else (if id < 22 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))))) else (if id < 39 then (if id < 32 then (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 35 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))) else (if id < 45 then (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))))) else (if id < 78 then (if id < 65 then (if id < 58 then (if id < 55 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 71 then (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))) else (if id < 91 then (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))))) else (if id < 98 then (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))))) else (if id < 158 then (if id < 131 then (if id < 118 then (if id < 111 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 124 then (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))))) else (if id < 144 then (if id < 137 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))) else (if id < 140 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))) else (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 151 then (if id < 147 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))) else (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 154 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))))))) else (if id < 184 then (if id < 171 then (if id < 164 then (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))) else (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))))) else (if id < 177 then (if id < 174 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))) else (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)))))) else (if id < 197 then (if id < 190 then (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)))) else (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))))) else (if id < 204 then (if id < 200 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))) else (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)))) else (if id < 207 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none))))))))) else (if id < 316 then (if id < 263 then (if id < 237 then (if id < 224 then (if id < 217 then (if id < 214 then (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none))) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 220 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))) else (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))))) else (if id < 230 then (if id < 227 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)))) else (if id < 233 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)))))) else (if id < 250 then (if id < 243 then (if id < 240 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none))) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)))) else (if id < 246 then (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))) else (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none))))) else (if id < 256 then (if id < 253 then (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 259 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none))) else (if id < 261 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))))))) else (if id < 289 then (if id < 276 then (if id < 269 then (if id < 266 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none))) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)))) else (if id < 272 then (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none))) else (if id < 274 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none))))) else (if id < 282 then (if id < 279 then (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none))) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)))) else (if id < 285 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none))) else (if id < 287 then (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none)) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)))))) else (if id < 302 then (if id < 295 then (if id < 292 then (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id = 291 then some localCycle00291 else none))) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none)))) else (if id < 298 then (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none))) else (if id < 300 then (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none)) else (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id = 301 then some localCycle00301 else none))))) else (if id < 309 then (if id < 305 then (if id < 303 then (if id = 302 then some localCycle00302 else none) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id = 304 then some localCycle00304 else none))) else (if id < 307 then (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id = 306 then some localCycle00306 else none)) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none)))) else (if id < 312 then (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none))) else (if id < 314 then (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id = 313 then some localCycle00313 else none)) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)))))))) else (if id < 369 then (if id < 342 then (if id < 329 then (if id < 322 then (if id < 319 then (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id < 321 then (if id = 320 then some localCycle00320 else none) else (if id = 321 then some localCycle00321 else none)))) else (if id < 325 then (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id = 324 then some localCycle00324 else none))) else (if id < 327 then (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id = 326 then some localCycle00326 else none)) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none))))) else (if id < 335 then (if id < 332 then (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none))) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none)))) else (if id < 338 then (if id < 336 then (if id = 335 then some localCycle00335 else none) else (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id = 337 then some localCycle00337 else none))) else (if id < 340 then (if id < 339 then (if id = 338 then some localCycle00338 else none) else (if id = 339 then some localCycle00339 else none)) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none)))))) else (if id < 355 then (if id < 348 then (if id < 345 then (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none))) else (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id < 347 then (if id = 346 then some localCycle00346 else none) else (if id = 347 then some localCycle00347 else none)))) else (if id < 351 then (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id = 350 then some localCycle00350 else none))) else (if id < 353 then (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id = 352 then some localCycle00352 else none)) else (if id < 354 then (if id = 353 then some localCycle00353 else none) else (if id = 354 then some localCycle00354 else none))))) else (if id < 362 then (if id < 358 then (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id < 357 then (if id = 356 then some localCycle00356 else none) else (if id = 357 then some localCycle00357 else none))) else (if id < 360 then (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none)) else (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id = 361 then some localCycle00361 else none)))) else (if id < 365 then (if id < 363 then (if id = 362 then some localCycle00362 else none) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none))) else (if id < 367 then (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id = 366 then some localCycle00366 else none)) else (if id < 368 then (if id = 367 then some localCycle00367 else none) else (if id = 368 then some localCycle00368 else none))))))) else (if id < 395 then (if id < 382 then (if id < 375 then (if id < 372 then (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id < 371 then (if id = 370 then some localCycle00370 else none) else (if id = 371 then some localCycle00371 else none))) else (if id < 373 then (if id = 372 then some localCycle00372 else none) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id = 374 then some localCycle00374 else none)))) else (if id < 378 then (if id < 376 then (if id = 375 then some localCycle00375 else none) else (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id = 377 then some localCycle00377 else none))) else (if id < 380 then (if id < 379 then (if id = 378 then some localCycle00378 else none) else (if id = 379 then some localCycle00379 else none)) else (if id < 381 then (if id = 380 then some localCycle00380 else none) else (if id = 381 then some localCycle00381 else none))))) else (if id < 388 then (if id < 385 then (if id < 383 then (if id = 382 then some localCycle00382 else none) else (if id < 384 then (if id = 383 then some localCycle00383 else none) else (if id = 384 then some localCycle00384 else none))) else (if id < 386 then (if id = 385 then some localCycle00385 else none) else (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none)))) else (if id < 391 then (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id < 390 then (if id = 389 then some localCycle00389 else none) else (if id = 390 then some localCycle00390 else none))) else (if id < 393 then (if id < 392 then (if id = 391 then some localCycle00391 else none) else (if id = 392 then some localCycle00392 else none)) else (if id < 394 then (if id = 393 then some localCycle00393 else none) else (if id = 394 then some localCycle00394 else none)))))) else (if id < 408 then (if id < 401 then (if id < 398 then (if id < 396 then (if id = 395 then some localCycle00395 else none) else (if id < 397 then (if id = 396 then some localCycle00396 else none) else (if id = 397 then some localCycle00397 else none))) else (if id < 399 then (if id = 398 then some localCycle00398 else none) else (if id < 400 then (if id = 399 then some localCycle00399 else none) else (if id = 400 then some localCycle00400 else none)))) else (if id < 404 then (if id < 402 then (if id = 401 then some localCycle00401 else none) else (if id < 403 then (if id = 402 then some localCycle00402 else none) else (if id = 403 then some localCycle00403 else none))) else (if id < 406 then (if id < 405 then (if id = 404 then some localCycle00404 else none) else (if id = 405 then some localCycle00405 else none)) else (if id < 407 then (if id = 406 then some localCycle00406 else none) else (if id = 407 then some localCycle00407 else none))))) else (if id < 415 then (if id < 411 then (if id < 409 then (if id = 408 then some localCycle00408 else none) else (if id < 410 then (if id = 409 then some localCycle00409 else none) else (if id = 410 then some localCycle00410 else none))) else (if id < 413 then (if id < 412 then (if id = 411 then some localCycle00411 else none) else (if id = 412 then some localCycle00412 else none)) else (if id < 414 then (if id = 413 then some localCycle00413 else none) else (if id = 414 then some localCycle00414 else none)))) else (if id < 418 then (if id < 416 then (if id = 415 then some localCycle00415 else none) else (if id < 417 then (if id = 416 then some localCycle00416 else none) else (if id = 417 then some localCycle00417 else none))) else (if id < 420 then (if id < 419 then (if id = 418 then some localCycle00418 else none) else (if id = 419 then some localCycle00419 else none)) else (if id < 421 then (if id = 420 then some localCycle00420 else none) else (if id = 421 then some localCycle00421 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![0, 5, 4, 6, 2, 1], ![0, 5, 3, 2, 6, 1], ![0, 4, 3, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 421 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 896)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 5, 6, 2, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 117 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 897)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![0, 5, 3, 6, 2, 1], ![0, 4, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 133 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 898)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![0, 5, 6, 3, 2, 1], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 282 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 899)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 5, 6, 2, 1], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 326 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 900)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 4, 5, 6, 2, 1], ![0, 3, 6, 5, 2, 1], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 40 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 901)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 4, 6, 5, 2, 1], ![0, 3, 6, 5, 2, 1], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 355 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 902)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 4, 5, 2, 1], ![0, 6, 3, 5, 2, 1], ![0, 6, 3, 4, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 171 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 903)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 4, 6, 2, 1], ![0, 5, 3, 6, 2, 1], ![0, 4, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 17 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 904)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![0, 5, 6, 3, 2, 1], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 324 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 905)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![0, 5, 6, 3, 2, 1], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 38 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 906)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![0, 6, 5, 3, 2, 1], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 149 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 907)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 115 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 908)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 366 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 909)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 4, 6, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 368 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 910)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 4, 3, 6, 5], ![0, 1, 4, 2, 6, 5], ![0, 1, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 33 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 911)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 77 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 912)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 218 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 913)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .low (![122, 285, 178, 72, 63, 345, 73, 62, 31, 403, 125, 252, 98, 29, 175, 415, 351, 362, 260, 258, 187, 113, 179, 276, 418, 376, 37, 168]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 914)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![358, 263, 131, 74, 155, 359, 103, 42, 54, 26, 105, 400, 307, 361, 15, 382, 44, 342, 14, 356, 190, 91, 393, 308, 81, 134, 222, 228]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 915)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 3, 6, 5], ![0, 4, 1, 2, 6, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 419 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 916)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 2, 3]], proof := .tail 77 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 917)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 3, 6, 4, 5], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 275 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 918)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 322 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 919)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 1, 2, 3]], proof := .low (![349, 285, 178, 80, 111, 392, 119, 62, 407, 143, 110, 347, 12, 29, 200, 23, 261, 362, 9, 185, 329, 141, 165, 224, 35, 189, 417, 166]) }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 920)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 4, 6, 3, 5], ![0, 1, 4, 6, 2, 5], ![0, 1, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 45 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 921)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 1, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 160 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 922)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 283 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 923)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 3, 5], ![0, 1, 4, 6, 2, 5], ![0, 1, 3, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 78 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 924)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 3, 5], ![0, 1, 6, 4, 2, 5], ![0, 1, 6, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 373 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 925)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 1, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 148 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 926)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 156 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 927)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 206 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 928)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 3, 5], ![0, 4, 1, 6, 2, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 0 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 929)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 3, 2]], proof := .tail 312 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 930)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 1, 6, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 1, 3, 2]], proof := .tail 233 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 931)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 1, 3, 2]], proof := .tail 142 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 932)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 4, 3, 5], ![0, 1, 6, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 3, 2]], proof := .tail 330 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 933)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 1, 3, 2]], proof := .tail 234 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 934)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .low (![294, 61, 310, 257, 116, 137, 73, 278, 202, 169, 1, 48, 98, 66, 381, 3, 67, 353, 203, 357, 383, 52, 348, 194, 196, 55, 159, 168]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 935)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 5, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 410 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 936)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 2], ![0, 1, 6, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 237 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 937)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 1, 6, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 177 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 938)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 4, 6, 5, 2], ![0, 1, 3, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 377 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 939)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 4, 5, 2], ![0, 1, 6, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 201 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 940)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 4, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 1, 6, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 365 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 941)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 16 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 942)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 206 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 943)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 5, 4, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 944)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 5, 3], ![0, 4, 1, 6, 5, 2], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 412 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 945)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 226 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 946)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 1, 3, 2]], proof := .tail 410 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 947)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 106 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 948)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 227 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 949)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 177 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 950)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 299 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 951)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 153 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 952)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 375 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 953)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 4, 6, 5], ![0, 2, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 85 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 954)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 50 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 955)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 339 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 956)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 213 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 957)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![4, 109, 192, 305, 242, 114, 411, 5, 367, 136, 193, 286, 98, 346, 328, 262, 230, 232, 372, 92, 273, 318, 317, 93, 173, 176, 247, 209]) }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 958)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 277 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 959)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 84 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 960)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 3, 2, 6, 5], ![0, 3, 4, 1, 6, 5], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 140 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 961)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 3, 2, 6, 5], ![0, 4, 3, 1, 6, 5], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 321 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 962)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 6, 4, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 2, 3]], proof := .tail 374 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 963)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 6, 4, 5], ![0, 3, 1, 6, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 57 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 964)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 6, 4, 5], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 56 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 965)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 1, 2, 3]], proof := .low (![211, 298, 221, 240, 32, 392, 119, 363, 163, 100, 170, 174, 12, 184, 100, 389, 380, 304, 6, 184, 184, 184, 251, 43, 343, 371, 198, 108]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 966)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .low (![350, 390, 131, 267, 214, 36, 249, 204, 398, 384, 243, 253, 265, 245, 138, 167, 236, 280, 130, 145, 406, 274, 360, 135, 82, 344, 76, 87]) }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 967)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 331 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 968)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 64 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 969)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 58 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 970)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 3, 1, 2]], proof := .tail 172 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 971)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 4, 3, 5], ![0, 6, 1, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 388 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 972)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 271 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 973)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 313 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 974)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 3, 1, 2]], proof := .tail 335 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 975)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 3, 1, 2]], proof := .tail 181 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 976)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 219 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 977)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 150 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 978)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 293 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 979)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 219 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 980)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 4, 5, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 10 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 981)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 401 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 982)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 315 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 983)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 226 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 984)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 4, 5, 2], ![0, 6, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 311 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 985)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 227 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 986)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 1, 5, 2], ![0, 3, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 416 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 987)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 1, 5, 2], ![0, 6, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 289 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 988)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 101 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 989)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 104 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 990)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .low (![250, 231, 131, 404, 325, 337, 327, 112, 54, 248, 385, 290, 296, 215, 235, 364, 306, 323, 97, 246, 210, 205, 157, 46, 378, 195, 164, 162]) }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 991)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 150 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 992)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 34 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 993)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 4, 3, 1, 2]], proof := .tail 410 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 994)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 2, 1, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .low (![127, 191, 292, 420, 295, 337, 107, 88, 152, 333, 21, 408, 20, 154, 268, 414, 256, 96, 126, 154, 154, 154, 264, 121, 352, 102, 47, 95]) }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 995)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 1, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .low (![396, 291, 397, 281, 300, 337, 107, 386, 269, 340, 129, 290, 296, 341, 39, 314, 306, 288, 68, 272, 320, 320, 409, 46, 2, 195, 132, 162]) }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 996)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 394 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 997)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 106 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 998)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 8 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 999)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 402 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1000)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 4, 6, 5, 1, 2], ![0, 3, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 3, 4, 1, 2]], proof := .low (![239, 220, 139, 199, 338, 53, 223, 41, 128, 188, 18, 90, 255, 244, 70, 124, 90, 302, 413, 19, 90, 225, 387, 90, 83, 90, 334, 90]) }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1001)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 4, 5, 1, 2], ![0, 6, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 79 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1002)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![0, 6, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 217 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1003)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .low (![254, 109, 192, 207, 144, 197, 399, 5, 24, 25, 186, 287, 98, 216, 86, 212, 284, 232, 395, 270, 354, 180, 316, 13, 30, 151, 75, 391]) }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1004)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 370 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1005)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 405 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1006)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 3, 6, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 319 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1007)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 1, 5], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 60 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1008)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 1, 3]], proof := .tail 118 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1009)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 89 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1010)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 1, 3]], proof := .tail 336 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1011)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 2, 4, 5], ![0, 3, 6, 1, 4, 5], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 183 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1012)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 2, 4, 5], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 241 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1013)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![0, 3, 4, 6, 1, 5], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 120 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1014)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 1, 5], ![0, 2, 1, 6, 5, 4], ![0, 6, 2, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 51 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1015)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 2, 1, 3]], proof := .low (![161, 279, 297, 369, 123, 392, 119, 238, 7, 27, 332, 347, 99, 147, 182, 266, 158, 304, 28, 309, 208, 69, 259, 49, 379, 94, 22, 71]) }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1016)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 59 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1017)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 4, 5], ![0, 6, 1, 2, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 65 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1018)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 4, 5], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 303 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1019)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 4, 3, 5], ![0, 6, 1, 4, 2, 5], ![0, 6, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 388 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1020)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![0, 4, 6, 1, 2, 5], ![0, 3, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 229 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1021)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![0, 6, 4, 1, 2, 5], ![0, 6, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 3, 2, 1]], proof := .tail 146 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1022)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 6, 5], ![0, 6, 2, 3, 4, 5], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 3, 2, 1]], proof := .tail 301 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1023)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (896 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 896 ≤ id.val) (hhigh : id.val < 1024) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 896)) = true := by
  let j : Fin 128 := ⟨id.val - 896, by omega⟩
  have hsum : 896 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (896 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard007
