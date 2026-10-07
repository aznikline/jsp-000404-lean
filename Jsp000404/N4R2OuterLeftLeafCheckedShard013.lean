import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard013
open N4R2OuterLeftReplay

-- Cycle fingerprint 00521f72536de6fae549ba98f60c026256a1dc5370d49df5dae1f46852ffbffd.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 014c56d3b555edbde55b66bc4984269eb19a79607b775c8f834e4e84a306d9ff.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 0223a589ad70eeb04e9378e98b1dc8e546101d29d639a55d107a9eee2e053feb.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 040f8e479b9e3c87f2b7360ccb9d20d945aa00f8e73e36dd944fabd5fd09db53.
def localCycle00003 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 04b081a9a96dd2ffd48d06047e693eb0947fc0539e571b88705b5ddc87ce6a6e.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 04e48b1159ee5accedab0d1f1d0ff521dd679b002263405f76eee831cfd0655f.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 05144428d8d666dab3e22de4af3c91728d46033ecbc47119b3ac4fb7b0313e8b.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 056be970e3c23bad3bdcfbccba693d8f68a8dc55ef8329788ec747900d7597cb.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 056d22a9891d7eb5a14624560d3d7551d37ba67b73bc048901769a754e6778bf.
def localCycle00008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint 06bfc8704aab047976c73a781c9a1c63f42bdf3f26ab509f4415a201f67c1c1d.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 075115116d09ffd0cdd20f5dc8a6ebd5e89f83858adbf19e71d650caa00a780a.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 15 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 07b13ce310877dd96c2ded4ab924d4fcb312c2d368ab33d7eb2110be6d9210ae.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 084ecb729763235ee8b12561f0dbb171cede355f75dfa5661607578dd8c79188.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 08620e9de650a01bcfe6bd01ca7a2833291abe2fecdd22eb33943e64400e585c.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 2, .triangle 12 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 08b4a54d2a160328e30bb09c2177dd1c228f4cce1fb5b1d338acb9ef80fa603c.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 20 2, .gapLower 1 1]

-- Cycle fingerprint 0c435c27adfc1f12555a10a6185d8b90d0e51b0c06e4803fcd8411ecfe2812dc.
def localCycle00015 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 16 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0c48d46f7631445603b3adafe5d9dc4be1b554d36ab13fd77becdc1bd25d242b.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 0d3df9f8f43f6d381c9c448a3335d10ace72209edeb21eeb51e9b4d1842a7b80.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 0d998254cb6d5b175b65d3d7445e39a97cbe52759d68bdec0d55f91895ea0817.
def localCycle00018 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 22 2, .gapLower 1 4, .corridorLower 1 2]

-- Cycle fingerprint 0e45493ef43cbda19f96b9ec7c590f5c837f2e6bc3b6c9da5d35728e5ece6119.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 0eaa91d9f3f9ad751d5716eae9c8f76e212a66132f1cd624b4dd0628c98f04ed.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 3, -1, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 18 1, .triangle 27 1, .triangle 32 1]

-- Cycle fingerprint 101b5a972a27153c39a7001ed80a1395902863b7b164c85c8ebf63f172b41db7.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 15 0, .triangle 5 0, .triangle 0 1]

-- Cycle fingerprint 10326e20ef947fdde0b257b8777eabf09114c975cd010ca5edffb35ef171b1fb.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 10f20961839520b140c365a972636f9a38530c68476ad59b858a53c16e3b483e.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 1197ad0bd9f1826a2d607492f520336a88f1a5251ce4dbf9794e4202c25cd064.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 120507979a825079b3f940cdd42e5c7120f76327d63555ca0cad714990f76707.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 122a8b6b0420c5228fdaf2f64fa772ce6c404cbcb9600661b2c6932281a0c202.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint 13617db116de09efdfcbe4e6572bb50a9ffb21b5a108586c4aba5c898f92a233.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 13e285cfe2d6db47ba55cbf94c79eca8d4f4178265b4ad9f410d39c55d57df29.
def localCycle00028 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 19 0, .triangle 25 2, .gapUpper 2 5]

-- Cycle fingerprint 140ab5db5a6346a7f16db39ecb6c6f33541e7ab76bb40701cc888beeb79b2331.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 142f6625b360c29a6b0a0479afa7ab31d849a38c288722bd63ad847f4e8e8d21.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 15ffda8b272e42a0b901fe3efea4a89c6d8ed9d42d289044ee0a24731b52310c.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -3, 0, 0, -1, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 12 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 17ceed8de7b44f004975b66118a91f5937a8fa4e701cc0070f9e7b68b9ef6d56.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 18825fe1c4e18cfe5a8007cd2253a26b04506ed510f84ec9bbf169ce2e8ba9aa.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 1d195639e1908cc911e1f7c2e0442ff899228aa8ee5e90e0555d3cb33ed1622f.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1dbfe66f9a8a5314850ed079a6948b4d0d3b91d638ef0d6a7bef8a0344304ba0.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1de8a4ec91b79a881ec817996fe9faadb045b8da6ee5a25270a24585332f906f.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1f783dad880d375bba98c8fe145c26f45e335007df6e4a536bc68ca17532b813.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 21001e32fdc49ed8aae07a1d43a486d6099d8662c4447998c263b8212046b080.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 226a48b877ba7242d85fd1ea0300c18f32ee345e3c730963cb78486d0f58eba7.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 23a3252b33bb997809eca313ca9af0fa496be914d49615603d587986c15103e4.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00041 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 261bf811aa0df56d8f9fe482d2121c9e5950b2668d94cc44770a001eb6af36cb.
def localCycle00042 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 1 4, .triangle 19 1]

-- Cycle fingerprint 26d004cbd8c590c6525b9c3d931ea397b826bcd8fed29cdf5918fef4fc57e462.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 273ce57af3e29b59ebe281d36d0569ec8d9d62aa98e564d4ef88c5b18eb7813f.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint 277593e2d20bb6301a0c752a06634e76942c50d5d08fbbc4a3298ac33fd3d5ec.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 2879a9ea282335b74ff44a5eda221018ea7637cf0b252e7b5496769b01dcb2c5.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 288248ca73cf81170c3acad7cde94193670ced8f24b4b39ebf05f8a0de07efcc.
def localCycle00047 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 288d809cd4af50a43528a0bebd5514a7829080227989ec7c6c815dae03739411.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5]
    constant := ![0, 3, -1, -1, -1, -2, 2, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6]

-- Cycle fingerprint 2a7aeb9b11eebe60ce872de95c9a4c742e8ae85753c6dabbe513d45a92262885.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2bba018ac58cfb2ee53b5952f36d181ab53255f7e826efde886f8b73da4d996e.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 1 2]

-- Cycle fingerprint 2bbdafa30bc5eef8c95ed9be279a6cb8d267ec949f3fda9f1d79048ac78373ff.
def localCycle00053 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .theta 4, .theta 3, .distance 1 3]
    constant := ![-2, -2, 0, 3]
    coefficient := ![0, -1, 0, 1]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .gapUpper 4 6, .thetaNext 3, .corridorUpper 1 3]

-- Cycle fingerprint 2c29e77a64a9f92a7234ee1105076f556a10873520b2d7140f4144a55d828ae3.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 2e5e0b1f472fe3e928c3d454d15014161b66d185197d753522f04da1cf7013e4.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2e6299350977b44ff55aff78204b6373f7aa5cd7da6e98aa18b54108fe790c0e.
def localCycle00056 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, 0, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 3051904ed865f88664cd15a117b8e40857cd01028e0e9f86b906dbcb287026f3.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 323ade28f8caf9f55625036b6468a09d417d880a396facf5892ff0741d400341.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3263f66f60639555d7f7ccbee43f3c822eb57899d7d919c1ace12dfaa927d81d.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3295a7a09004ae0284bf2f3e7ba9d09d65bed005921b2ca197a066994e7d1085.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 33269564ce4201f717310950b9f0f36726ee96227190ed97c6e10336e9ff4da0.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 3329bc0c72ffd3ce4c1cfa12fef0fc0b53b547427012ef59d83bb2b3c09f6360.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 332cc52b7029845fffd531f30bd5044cef76231465d7003a6fea911e467a4710.
def localCycle00064 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 336b59420a2e659b178441175c930f26636bfa91207a9f0af30a1e3ff1e7dba4.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -3, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint 3420f627a5e67af9a45acc48db20c4733c2d13d05c9c7df455e890ffa0a0497b.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 349c8ebd262bab22065838587466fa9b7a1765a383b0ead08762cb083e3b8c0b.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 357eb6b0d6e9cce2cffc9f50600c3aca24692be7f113dea576f88fce9d659a57.
def localCycle00068 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 35a6277855c7c950dd69693057ab3639ea252aadf0a958cc3dbd6848f9e43eb3.
def localCycle00069 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 35b3fd3b16442ef5763971a8a31737052118e857f8ec7f2b06b7132a77b5f148.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 36d3d2ec93a1f39ebead2ce90e1a82b2cf08a67498c71539cae35b75e1659f26.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![-3, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 370728bd35eda36a700f60eccb5b8c2962c7270749d01a874b139b8ece9fe302.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 372470ef793bc116f78e71869ddebd52d05acb58e8fb2429e65e601efd28e594.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 37563f5bff8fc689f26bc0dcf8d8973f3b3e247c80d7852f15ad9b5e157d93a9.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 2, .triangle 23 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 38c598d866eb75db5f9a51ba6687c3527c6ba1f4a8f04702f32ef23bb1a2222f.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, 0, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, true, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 3938f3a2c5f8683222e8f72064032b05ebea7511bba6545a11e6166d49bcaaaa.
def localCycle00076 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 39dcc7ebec18d24fb718be91bcfc3548f8f866fe8996ca6f7cfa5b5d31518c4e.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3c1a9bae1abced6725cf0f2c2fcb11a4ac1b1debe63231a0da58603ead699ec2.
def localCycle00078 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 3c8b912bd885edb7ee80f40b990162e4e295db0de09fecb4fc59083ece91e01f.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![-1, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 0, .triangle 29 1]

-- Cycle fingerprint 3dc55199b08e923759dc8b96a65993e2558f1b847f34406c43cf9dc98dee88f1.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, -1, 3, -1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2]

-- Cycle fingerprint 4027453bcac4f345a3f79df57cd88bfbaa2e5843a4317e203c7e5fc9433f77a8.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 40b1a928154ff6dc5441fda8b5bc199a6c204c928b5453fce31b7794f2fb813c.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 415f9647493b0f538b43926c705581747936ca73fc2479242242c7e3eb3669d3.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 41de3557ab8a97e595823cf8822e6912222b2d4c676e55324945f55de6b6688f.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 42cc1e4bb069f97b639438bc12b5a03d3b8a4b3941bf2f482ba573c49db559f7.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 42f243519d67e2842d3384db7831e849966ec654a4fcea6c7c75512fa1ca8430.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 26 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1]

-- Cycle fingerprint 4336545a4bb5ebd11157b05ab8c584afa1a8784c802f48ff17e8e9c29eb30b6e.
def localCycle00087 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 434b88f42fe7dbb4654797a17d589af325c67d217b4b2c43de7a6bb055a745e9.
def localCycle00088 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 18 2, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 43ea03350251aa6ed34fe0aadba2df70daeb06de652353eb4b222563a45fef78.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 459f336ef917660098e7e314e47969bc583fe9eef008a2b8d280baa8c6613b54.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint 46088c43c7fdbcf0853a55a2953b7433fe9ed9810fb65fde798849bcd04a5828.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 48231f6e96ee9b7534b50bf49ca52027e7b4914a18fc4117acd8104141a5aab8.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 48424aa43b3e80a07e234456e811e5b2bd0431c25f047086b1eb52e0dab78538.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint 489acfdf238afeb443bf7c2086f57fc32eeaff9a5104334426197e500d3fac31.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, -2, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 19 0, .triangle 25 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0]

-- Cycle fingerprint 4980114a8f81f864eafa7a8a8152a81025171242ea6d34f2b1f94e7cd2a772e3.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 4a218464fa737915644043ab233bf364e0f0102fd9e4eb21638c8a61bad4a710.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 4b4af92bba486f99b50dd895357772b0b6dd4266c5184ca53629c53cfec748dd.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 4e069421ca1f86a3e1ad47f7266a09a0be3aaec766e39492865dfdaa76488d94.
def localCycle00098 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 4e611817b5d5c20cfd8816b50512462ee69b7d000954a2a3f18dd13c2fb97ace.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 2, .triangle 3 0]

-- Cycle fingerprint 5031e120fefaf5029fd53e2820eaf1f5fb5f6cf80ec7b60adbe53a9b1588cc92.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint 50391b31f056452a728307c39e475e6aa3a6df8b73ab5d1b1b5dd16c94a89d29.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 54507fcbc414d791530c1e7de2294201ce18568fe9c3d349f83b26f74d6b4af5.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00103 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 55e01f3d0d39558379bb5ca4dc1c26fc2d49c33116eb520c0041df1926262347.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 56e894358187601b8a71251b475217b880067d4df9f75126817b0fa990f1eee5.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 5a1b98ace6110aa9199ec277e0418d7859043a291f9a08105c48a80bfff83560.
def localCycle00106 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 5c171c567be61c4b094ceb085d4f5d2e90f246ec48c6cae7b63bd1fbf8a4b00a.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 5c5f31992d733c23ca381660d973decc6636788c5b155f75b6a4271c15453da7.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 5e760f9e6662264d7c376dea3bfb881ac9f73b1a80bf375603649b0c20cf8a6b.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5ecdb076cc5ac968f8dc1c64411aabecb72a681005fa136ccbb3856c1c2dc3ad.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5ef0bcb46d06bb8c417169729345b342fd66b5d69d4dd37e37f1cfacc1501c6e.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-2, 0, 0, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint 5f6a7245e239e58274c097227106b1b0fe885072f9c9a59721b66b092f0fc767.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .triangle 5 0]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 605d71e2cd0dd8b75ffd899fb67281ded0bca34e769823cf977c2b9c1f60df45.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 60a13dfb08b673103fe413356b0e611ef6f8d2f94f7b984874afbbdb49c19c54.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0]

-- Cycle fingerprint 613ce8233816ad106c73e081e76befa6e9eea2d0c4c3aa1c1442d42c917c9193.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3]
    constant := ![-1, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2]

-- Cycle fingerprint 61dcfcb9c2f2986b66a9d111a66c0f1fe297ebf0f3de64796242be9200f9dab2.
def localCycle00117 : Cycle where
  length := 4
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 33 2, .triangle 21 0, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 629c89657a5a430557e53e3d624c85571149347f037d89733a8ccfec3ff92dcb.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 62b5b7bfb520210bc4ed8093720c5e50b1f4d4e57b7f6e764377db594891c520.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 63846a691201283778a478d0eb28929a6b13e4e360899ed606ce2a70ae5bde26.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -1, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 6405df57451a5c7215e5f02d526f7845f70df0946466eb64eed6693e9d6369f2.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 6413f908e8d2c6d1dd33913fdddfa57736e43c69c6c8e6350b5c1a7cd83bb255.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .triangle 21 1, .gapLower 1 1]

-- Cycle fingerprint 64bd5d57567cdef23915eaaae806dcf07c28028324e5283522a08d066467114e.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 64e4928616c1f92e380cb48cd34acf6dfe53bc46f02ee2cdbcebab1bc835290a.
def localCycle00124 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint 659da8a4fba86144f83311b71da6882c873b3f284f86be34912dc601d76af0ea.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 5 0, .gapLower 0 1, .gapLower 1 0]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00126 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 6676a36c73d5564d94f61dc6e664a0b570919ced66feaee342fc536d30c3a0c0.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 27 1, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 671f502bcf286a19931c6a655f026ff9142ea2cca180c491bab79186ca4a1844.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 67cdaec86441069a6a1d7e402136ddd7c523b8214acf7b63435c2e63dd427cd6.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 1, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 68d2d7b221a7e35815ac2366a0ca4143ec76730b90da02ac0500b7f5dfcdb9a9.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, -1, -1, -1, -2, 2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint 6a652f4312e6f0d8a465da9f3cd4241f6df0a6dca56ff1b0d1382d2920d70b8e.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 30 0]

-- Cycle fingerprint 6a6f9e36f568723fc4bf9f6aa4ac4266117635ca0e0cdbaff163ee523aeca34f.
def localCycle00132 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 6b0bd716451bd1b31ddb6ae7428ef5dfea2143d5c8ca347fa385470133026c9a.
def localCycle00133 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 3, -1, -2, -1, 2, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 6bc54df36104f13818d70a72d9966eee38988e6f179ede0dadb25748cdf8cfc9.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 2 6, .distance 4 6]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 0, .triangle 29 1]

-- Cycle fingerprint 6c139782f6444b39a258067205a3441b555a74e19308ef1b1cc2f88412c5ecf8.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 6, .distance 2 5]
    constant := ![0, -1, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 2 2, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 0, .triangle 29 2, .triangle 30 1]

-- Cycle fingerprint 6c67051834f247c950ebc339abbd79382ecd400f7ded275a60089973dce23757.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 6cba3b2dcd34f2d43c8e631eb4e3baf02da65eed875149c0007bb7bbd178afbb.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, 0, 2, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 33 1, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 27 0]

-- Cycle fingerprint 6d06ad787746708ed2f42e640cc4e8470830bc64d572b792f627031376c035e1.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 6d075645e78b09d1727b1fd05be3f8c985d5d94be8200383224ee30ebe0fb442.
def localCycle00139 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 6e33e3522674ebfa6fb8cbba2bdd9a49ff01d9f1905ee59e76129362c7195955.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 6fdd979a52f1b5bcb658130c4c50de86e730d62719573700669b192b283091a9.
def localCycle00141 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 19 0, .triangle 25 2, .gapUpper 2 5]

-- Cycle fingerprint 71511d93ba5986cee87d2caa4b0493d7d30d85b11ad89a51478e2194f856f94f.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 717899c9981747b0fe5f642a4280aed0261fe6a80bf7e119bbfe074fb3b9f34c.
def localCycle00143 : Cycle where
  length := 7
  data := {
    node := ![.distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, -1, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 71ea96193659485efc3c2cddaea6bad28a9bbe3fc41e7471fedc68847fdb0705.
def localCycle00144 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 2, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 73f028b8165c84340ef330b85e66187ec19edfd7340563a62df9b3951c0b8fb5.
def localCycle00145 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 752379fafe9675a470b05178f11e750d0f4f9c43017c2adbbada13114d3aff56.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 0, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7549d5c400d5eac0bb30f0cce2c73326d425ba54a48809fbfa28f424b8918018.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 758b093560ad14dc2fbc18de69cc88cede70996cca66754dfc6730ec8679530e.
def localCycle00149 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Cycle fingerprint 75b7cd0080cac80e88a9cebe30b1ab38cdaa67003f15a02e75866d7f9ff0bc37.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 76174a6fd7524be8ec8fbf5ff5d146737fe60f4f9b4dfd5bf8b15a09f8691fd4.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 23 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2]

-- Cycle fingerprint 76bb9e5a22cb1c132fdc35535fa2fe032214cc3136673139bbb4cecbc324ad84.
def localCycle00152 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3]
    constant := ![0, 0, -2, 0, 0, 3, -2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 26 0, .triangle 10 0]

-- Cycle fingerprint 76c6ad3bbf2c1b9d5aea92aa7d2abd2a5432bb599c9146c3368e78eb4b369160.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 9 2, .triangle 13 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 77eb55cc3ac9e603f336be9563063a5b9907de29397bce6549fb5eca0cda7633.
def localCycle00154 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 78725dc908b7da6786e24bd0542060bb6abffe307149ae15c7dedbaaecbae246.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .gapLower 1 3, .gapLower 1 2, .triangle 20 1, .triangle 26 0]

-- Cycle fingerprint 78771434bd30b2ee7159f616d3dcb16531d38a988cd29a3230e9bf9148be9567.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 7bf973dce644437a470d1011d2be0e1f1cb2080c4b9ffb34a815700f480e99a9.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7c8d500fd6af7bdb36a297fcb7a569e4479911548b95300a4d3e562c14f53839.
def localCycle00158 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 7d05747694101b4f5a8e5bf2d59abfafec35f2ab35f3fa32fca97f1ba73d7f75.
def localCycle00159 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 7d4faad445fe41469bbc796c0c57ceed04694d3088d9fda4a5d3bccaf7e15886.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1]

-- Cycle fingerprint 7dd8236cd31226ebbad644d511d485e3c84979e589594cf11ebd49f47665cdcf.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 7e92b312b16b672b8eb603dd440f4c9003da7dcd93b2fef9f04b15a13637b91b.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 26 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint 7f3682f97edf3e7144d93c3439f577aa9d67b723cc019765ef13d3e7e29899cf.
def localCycle00163 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, -1, 2, -1, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 19 0, .triangle 21 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 7fa07494ac197971d658b7c4b2855b93c4613db5e7da9be7897dec323f148c85.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 22 2, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 80c054f41a5aab00d08d0f06849060b558b82ea9c5985f4a06536de154c77995.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 1 3, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 84273045f7d124f22f686249ff73cef55bd1de4da98900feeb7e5afff25d62fb.
def localCycle00166 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 17 1, .triangle 18 2, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 8645c85b13f5468aaa52b98cbcdd1133eb1f4715bdda5a1e30976392efdb1565.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 4 6]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .thetaLower 4, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 2 2, .triangle 13 0]

-- Cycle fingerprint 864796e1e1359bf6550f0a21904eaf943591ceb6d0898ddabc75c623b7806578.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 86bef04538bb77a1fcd2dc42b2226703e9269b3a876a8a89aa4047fd85954e1b.
def localCycle00169 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint 86dbe340c6b6ae3b3540d6bb4e8ec0e3ffbf68d9543585a0df91fd214d579520.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0]

-- Cycle fingerprint 8a587f70b50aab7a367bdfd1e9f51c2ffcdede6c0a450a5b5508e8cf20fbdcf4.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 8a78476dd0803bf2c8f4521413e7080b5241826553981bc876406ca79d52e523.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, -1, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 8ab1d77a62515b1494b8a97b556b5c5bd5b1535fe38502f15967b0be5dfb477b.
def localCycle00173 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 8ab759b426a3e7803bfaada12603ffdeb6210275a12e69a3f9eb0771bb4ba9d1.
def localCycle00174 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 8bbb0043189a8a353bbb1cfc51e69f68c9cd1e0cfd040bb7c3240609792454dd.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 8f579fc1f3f883c65abfae81c6b1375d56ad48d69a1e928c9289ae35cd5d3c39.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint 9088459cef845b91c32dbaa0722fe246bed506563fb33c422e70a458cbcf960d.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 91d3bf5f8bfe64c38d29a0062a88989478d12ef55e628ee769a3ea0596758fc3.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 91f9af8b7d726399c6daf8ef835de51136753d31004f60c331a9c9a478756841.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 939a9f65243e155640b536c64534b5936ba0d858afbe1ffc83afe3a937c98776.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 94071fbb62ffb0fb71d1a860499e4f7c7356e266e168f1e4456312c9a07dfbae.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 947b4b7da31d6582238fe0d39565c0b6853893c6b154eb99fe2b5d27e07e0e20.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 95c1caf100df4d65016a487ae5857a571c9fe144f9ba131682d46cc3cdd3d270.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint 95d67239f08f5b0659a31cb606e706d941926e9537c12b18b471a55ba3d8b1bc.
def localCycle00184 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 9631c61696057be809bad521d754782b4850f965b5db79343f61d320043253a4.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .triangle 19 0, .triangle 25 0, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0]

-- Cycle fingerprint 968dfa9d10f961a9f0046706a28fbeac28978f1ddbc35463622efda303289e18.
def localCycle00186 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 968fec239115fb554919b5e189fb5de6a19f0c9faf02b7e8021c2b69408661e3.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 973f6d567d1135534acc13122e39fc4e2ec7a818389483a5accb50657177f304.
def localCycle00188 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 15 2]

-- Cycle fingerprint 97a5a7ba044847c0e15c3ba57fc9d884ad956dbad35dca7b4efa2e573027319e.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2]

-- Cycle fingerprint 9808c4ef15ced420488e6f366eae4d64eb6e671d7fa741ee3b132a8ff3417b00.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2]

-- Cycle fingerprint 98e76b9fc5a0dc26a5916ef54198df39bb27dd9763d877b2e69962582736ef03.
def localCycle00191 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 98f5d2bd7c0793ec744dbc333c229f9919eba9b7df8036ded7a1ef5403f5e5ca.
def localCycle00192 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 9a05ec3c9c4b75c5623b2a8fe0b34fc48c934105ff6c50d481e085ca51103f12.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 9b210f9b0cd31882d2375b01ac954a22355a78895d59e91bb6ff5393add360aa.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 9b828e6cab49028ce84e20f9369d7465fa98b665f9226d466b11a8d0e41cf76b.
def localCycle00195 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 6, .theta 6, .theta 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -2, 0, 2, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, -1, 0, 1, 0]
    strict := ![true, false, false, true, true, true, true, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 2, .gapUpper 3 3, .gapUpper 6 6, .thetaNext 5, .corridorUpper 3 5, .triangle 26 2]

-- Cycle fingerprint 9c636b2eeb3bc0a8bdb7314c0fc61868b6b66d8cd70307f392fc44bc98a27302.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint a00c14c9538a435cce2fd9358a38550bc8f7422e4c81a53501f93833da32ecc9.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint a00d9900c77e946d6c053262487b542e6204c8ee92033f499d2b2c75116fd869.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .gapLower 2 1]

-- Cycle fingerprint a02cde57ee5470eba11e6bc08660a7dc78ba95d481b5b086fdd2051217d015d3.
def localCycle00199 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0]

-- Cycle fingerprint a05faa4cba0286962d2c4ba58c50fdeba18755230ed43bd378e4f93c6a68efa1.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint a17b97e6522872fcd9e25411dcc9481ac452efd3d11cd48ca3581a5e10557ab5.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint a285fb28fba0b1d4ffce8893f8a76389477919d1609a7c4a6dc126bdc0669bf1.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 19 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint a2ef511ab6bd370d560ba8fafbf679f87291bc0faa30d0a0aa5c333a11c9c375.
def localCycle00203 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint a331ec7303d023717fd3ccc0d591bf611cf746fd1eb7943ff1da06506ffa16d1.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-1, 0, -1, -1, 0, 0, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint a332cc410deb91f07134445ada3e760867883e3c9d823437a3243988b525d9c6.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 8 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a3916fb8576a4e16ed91f4e469b6bd1b1ae938b9d2502cc4c625907dc9010ec7.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a4abadeb2614dcbced2c9ce05a1400ebf896d29aabf5dc70ce2afef6d8a34869.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .distance 4 6, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6]
    constant := ![0, -1, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true] }
  origin := ![.triangle 13 1, .corridorLower 4 6, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint a4f92db99d01c5f146eaab8c359a0b784a756fbd14285d5de880895032cc05cb.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint a6a32800c0d29f62dbeb82dc62653ee5ba1640d44b915d6f17307f3ce952a4dc.
def localCycle00209 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint a6ac85c8dad49f65169960ac8cea837a4d7ac4a3cc08a1e2b9a1518e30a39cbb.
def localCycle00210 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint a9e70f1ba65aca628afc4ff3c7688cbf3ff3d188c3e184933c275eedfce79c7f.
def localCycle00211 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint aa57485b10a9d34fe62af4f8698a400b8a5df86272db25d030b7bb0572c6a1f1.
def localCycle00212 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint aad4ce51e31483ebae2cda51b9f3bc76ebe8e84c962848d0e4303d8fd5f975a0.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![-2, -2, 0, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint aba20f2ceabee11cf2ebfeb7d0b5f50381ae0e6d8d3edda22dfb4e99b4cce4e3.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 2, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ac630f0309d7b65ded0de39ff7fc8c0a582a5937f2cd7e1b7285e12962f35972.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint ac63858f3405cc256e61c4819b2774f7602cc4684f9bf5ae68e3cce2fcc99651.
def localCycle00217 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint acbad68fabae1f357106d60cf43314335b5eedc7409d7712c7a54ed3db5061c4.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2]

-- Cycle fingerprint acbec754095bb53c7b4f2512e1730fbe7aca5aa6458aeea8e958e3fa50f5d8b4.
def localCycle00219 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Cycle fingerprint ad84e992d12c601d8aef6f91070aa08c78028c10c27823d83680ee55d004fe11.
def localCycle00220 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint af90bc0d8c0fa9bba21bcac11bb81a6720644d14a6efe687873b5ca33246711b.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5]
    constant := ![-1, 0, 0, -2, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 26 0]

-- Cycle fingerprint b15b72f8189075089648677e021057b43a8e75bb6484be7d3ba2b7b4337bd8a7.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint b32682dd1c1aaf5bafa90b913015eae50f443419d52dd3364986e2d480cf681d.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, 0, -1, -1, 0, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, true, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 12 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint b34cfb258bc4b3b905e856b1398f38efd94f4c24081476c0be74fde84e8be09e.
def localCycle00224 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 5, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint b3f526d2b4bb859e48cfee7d0de07c558f0d9017bd1d7c1d37a6f5e5b40e193a.
def localCycle00225 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint b76f84521ac68ecfe4d9e3f851ffae69e215ebf00bd805f49893fb970a55571e.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint b94351ae4a8257e7a5d263f5af79040167e9469530fc5b52fea3eca95a357053.
def localCycle00227 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00228 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint b9ddeb734db6244834047858d4736d11c8bed434c1e4481bbcc8acf8865e83d7.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 34 0]

-- Cycle fingerprint bb7249eb6c10e3dc1cc5210d61e58180156c5bf97d65269f0a20bbf6d851ab97.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint bd226e0c629ad0797a9bae6805b15a478cc526faab269775dbe6bc49bd1d1f09.
def localCycle00231 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint bf34313b7ae585059aba07df6114a947cb08e218d1c68d013b55ee8bdc86dd01.
def localCycle00232 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint bf3bee06dfa54e0c97e0645c80a7bd04574d4d598beb115ae1b889c83b3b3d07.
def localCycle00233 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .gapLower 1 4, .triangle 18 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint bf3ce67ab7df63f40e52956ffc01d132df0905011b4852d7f7427691b3f7a04b.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint bf4f646a0fb5750a5a59ecbdbea96c39298fb1b9951decd69607f46b0753cf77.
def localCycle00235 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint c3fd8164e987bddffd4f595c33ea128ea21e13f7ce778fde9a501d59602220e5.
def localCycle00236 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint c523925cec2a96bc8c4570346ed39c0bcd9ededffa5d27633b994334c25a4667.
def localCycle00237 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c580eb741dd8ff97b99541354baf25da0af15cbc6654d9df08c3d8bbb8dfc2cd.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c597f235b9ec9c5b5e2d2dd25844070d6c5e7f4d35d8433dc8dd7e8029c5b175.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c81bff3a4af1d86b238d238ee9d85bb38610ee110d1d9ad536244cdcffcebf76.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint ca3fba20fb27df6a8091d77b32c7dd82941d7a8ddfd78c0a9ff730d9fd05a823.
def localCycle00241 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint ca549de2c8bd1ce05084dc2d3aeac9d060c95cd535042a4c44c1be0734300148.
def localCycle00242 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint ca6c704cfacdea34c5c093564587875cf841512611c1a8c543d0d42967ec22e6.
def localCycle00243 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint ce42d1ec757a5e256a8f5f8ccc64c09e09335e54678120dfabece3173307d513.
def localCycle00244 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 3, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2]

-- Cycle fingerprint ce7eac70bacb67eec2af6111238ac1c29f8eaabcd027f39a29ac7ed39c135144.
def localCycle00245 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint ceca543f0dcca6529696c113005b45be2d4c061a337988f993d8d894b36ee046.
def localCycle00246 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint cee643d2db74fb9f6be9d9a6a2910ce0d716edd4bda9b28ecaf47f3c8f861d0d.
def localCycle00247 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cf65d6d7fa3c39c6e36c1982081ffe25f80ccf85a072fd258218c1a05e90c956.
def localCycle00248 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint d19ed8ed589c29cabf9cf321132c031117d4c6015f18c7ece2edbe5f60aecaf5.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint d5a989a0aed197970196e7b3990b5da169a3ddb817203fc6c619d7b1994d1f3a.
def localCycle00250 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint d5f366ae48c1cfad7e6d7d69f482bda8746b640b4ef5543b52e870d56a444837.
def localCycle00251 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint d5f40763bb168e318e78b818383954500ffe3337ad609bf91b101a596794b4df.
def localCycle00252 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 2, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 2, .gapUpper 2 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d7931389e17c9d43bffce3a8910c86c057142abee0570370220cce04a3d09979.
def localCycle00253 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00254 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint d9b82c445a0f7a63d5bc0e21d72fd87dbc1004ae0096c8136f25caf9a7bcbe35.
def localCycle00255 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint daec27b8a60946e102a0469ce3ea6c443c8d7b19d86ac1249a8bc2079132f92c.
def localCycle00256 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint db18484c8fffe4ba573419e0e735c11c24b409ad80ce01d435914f4db17f0c3f.
def localCycle00257 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 0]

-- Cycle fingerprint db50cb21964ee201ad2577272d306bc234bda0327e03b92dd9d5a5c88c22cf7a.
def localCycle00258 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint db6ef3889b55eb491eacd52aebb80f08a779003398017fdd5201365495b4595b.
def localCycle00259 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 17 1, .triangle 26 1]

-- Cycle fingerprint dbdf8e8b577f97fa36d84f1f96a545d6197f0861b72ed892b054f8e5d23957f8.
def localCycle00260 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint deb393382ee3b0ca7b8043743f5cb5372a96066e8985bba225acccf0c8a24f4d.
def localCycle00261 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint df30ab2612525d319ab5872ba35ae8186ea20fb93b9d0810fe85d42bc2809fc5.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 6, .distance 1 5, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 23 2, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint e031c7daa302223b6e911ab67c86db8e30dbb847d2227016d791777fa712783e.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint e0482e3948eeb4ed6743ad7220b6fe6241fa972866518d0a89e45bd0a8c87ff5.
def localCycle00264 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 15 1, .triangle 26 0, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint e1212cba1de0320fd65a6ed62a1bea073ff44624fd3b3b922be11412c8146a45.
def localCycle00265 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00266 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e244521a55a43a674d54ba366c596d09973fe6ec7d5a007ecc11abec71bfe704.
def localCycle00267 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint e2760a33dbaa325cfa0c365c8838d810405e75b161dd5634b1022431074c118d.
def localCycle00268 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![0, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 17 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00269 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e453da6aa5fccb9e97f3eab0541e1bc95a9d759528a958d3d3ed808485a8e6d5.
def localCycle00270 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e5846869489d0e4eaca3f1d43500bcc36ca973d0e4ac6a8c79330f477ef04af2.
def localCycle00271 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e6268d33e362e5af2177659b0aa23bcd55f15f7e34e35e0dbdd51dfaf38b0087.
def localCycle00272 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 15 0, .triangle 5 0, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e67657616e3e494d71853a3b756483478e62198129a837a09ec60a3727713538.
def localCycle00273 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint e7ac0864d255561784076f70dbbed8e4bd0b5ac94f65604ed8289d597fd4e483.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e87f0de43ae23f7328acb6598cd1c1364952af1042353e5df82f8a5eb18ed5b8.
def localCycle00275 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 16 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint e8cc1e235c0358f3a3b088656320dfa9a540338aae36b1a4c7f5ab48455d3bd1.
def localCycle00276 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e9e326c259aac1483b9b6d93160550c608ed3cc8ea4d3c583f260f09456be2d5.
def localCycle00277 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00278 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint ec846b2c4e33f00df78dd8c2bcfad49e8f042dd103d959e0cb635a19d6ea7d2e.
def localCycle00279 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![0, -3, 0, 0, -1, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint edafea539b42b206123bf74a2e4923ffbe21c357208850addf8cdc007350a74b.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint edf8e68e7be57aa95717b51805d083b40f0193c91fefe6a8ea7cb8b89687cfb1.
def localCycle00281 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint f2706841287d06f2f8a8629870baae07113c20e026e52ca6518e960291db7881.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f30ba8f38d6497019f3ff1e2b4c7dcf0fe82873dc7413c49c636836cc0e29675.
def localCycle00283 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 33 1, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 15 1, .triangle 27 0]

-- Cycle fingerprint f431c49709af933635b8035b70f6b6c3c3a2ad39839701763dcdc35f7553be37.
def localCycle00284 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint f462f33e2e22cfb0602fa47081d78aed6b2e7c0d4b836d069a7b3d83dee3c559.
def localCycle00285 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 33 1, .triangle 10 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 27 0]

-- Cycle fingerprint f468b7361d130c4f9bcf0140866bb6d01f33291d2b3a1597020a9e83968108e7.
def localCycle00286 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![0, -1, -2, 0, 0, 3, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint f5d49a280817d08db13e784f24359c90431e6d34c359200854c33e3485bdc64c.
def localCycle00287 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint f7a277f0e90c6fa0b34cf9c49d6bb44815bceb740aed79c0cd50cb4158c32d1c.
def localCycle00288 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 1, .triangle 27 0, .triangle 33 1, .triangle 10 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 0]

-- Cycle fingerprint f916cc537e4bca96fac2ab6c97a7fad1bdb2d3abeef208ecded2ac621ecb7b35.
def localCycle00289 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f9d98cc6efcd710320f1ac47fee71d6f2345ffea9769bb159e85f8eb551d7e2d.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint fc02bb9bb7145eac7e56caaec55f388dcb7f577d80db4737ef95b90fa88cf3c7.
def localCycle00291 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint fcad58957fdc0db7cffbd384ded682e44e696cb132afc5123bb11f5f7ffd2aca.
def localCycle00292 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fdfa5edda279c7d0b920f59f7d830e689e53d4d0777b9409eb3dc1089a667d31.
def localCycle00294 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 2, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint fe35d5e8fdad8bd881cd256d1c7041fbcdb9e45c54477225001fbe2d8ca62fb0.
def localCycle00295 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 1 5]
    constant := ![-2, 0, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 21 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 22 2]

-- Cycle fingerprint fee0b77e2ba9aaf3eede1099aadc784764eafcf468b317e7e3708fedcfdf146d.
def localCycle00296 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 6 4, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

def library : Library := fun id => if id < 148 then (if id < 74 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 55 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 50 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))))) else (if id < 64 then (if id < 59 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 69 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))))) else (if id < 111 then (if id < 92 then (if id < 83 then (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 87 then (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))) else (if id < 101 then (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))))) else (if id < 129 then (if id < 120 then (if id < 115 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))) else (if id < 124 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none))) else (if id < 126 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))))) else (if id < 138 then (if id < 133 then (if id < 131 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))) else (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))))) else (if id < 143 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))))))))) else (if id < 222 then (if id < 185 then (if id < 166 then (if id < 157 then (if id < 152 then (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))) else (if id < 161 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)))))) else (if id < 175 then (if id < 170 then (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))) else (if id < 172 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))))) else (if id < 180 then (if id < 177 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none)))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))))))) else (if id < 203 then (if id < 194 then (if id < 189 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))))) else (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))))) else (if id < 212 then (if id < 207 then (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))))) else (if id < 217 then (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)))))))) else (if id < 259 then (if id < 240 then (if id < 231 then (if id < 226 then (if id < 224 then (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)) else (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none))) else (if id < 228 then (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))))) else (if id < 235 then (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)))))) else (if id < 249 then (if id < 244 then (if id < 242 then (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 246 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none))))) else (if id < 254 then (if id < 251 then (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none)))) else (if id < 256 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none))))))) else (if id < 278 then (if id < 268 then (if id < 263 then (if id < 261 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none)) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))) else (if id < 265 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none))))) else (if id < 273 then (if id < 270 then (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id = 269 then some localCycle00269 else none)) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id = 272 then some localCycle00272 else none)))) else (if id < 275 then (if id < 274 then (if id = 273 then some localCycle00273 else none) else (if id = 274 then some localCycle00274 else none)) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none)))))) else (if id < 287 then (if id < 282 then (if id < 280 then (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none))) else (if id < 284 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none)) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none))))) else (if id < 292 then (if id < 289 then (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id = 288 then some localCycle00288 else none)) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id = 291 then some localCycle00291 else none)))) else (if id < 294 then (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none)) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 258 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1664)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 184 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1665)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 37 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1666)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 2, 1]], proof := .tail 37 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1667)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 181 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1668)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 5, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .low (![249, 278, 186, 280, 1, 66, 103, 215, 27, 73, 239, 273, 135, 2, 17, 260, 291, 254, 160, 112, 43, 97, 136, 0, 246, 192, 15, 167]) }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1669)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .low (![116, 208, 68, 253, 1, 66, 103, 270, 263, 296, 239, 273, 135, 236, 78, 260, 291, 60, 276, 132, 132, 132, 136, 0, 246, 192, 15, 167]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1670)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .low (![252, 228, 227, 41, 178, 66, 103, 266, 176, 12, 255, 244, 126, 100, 238, 138, 40, 85, 200, 138, 40, 277, 131, 96, 124, 232, 83, 196]) }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1671)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 194 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1672)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 191 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1673)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 59 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1674)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 3, 2, 1]], proof := .tail 191 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1675)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 1, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 157 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1676)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 1, 6, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .low (![204, 90, 199, 8, 190, 66, 103, 267, 203, 264, 56, 152, 221, 209, 217, 110, 14, 179, 76, 209, 209, 117, 189, 10, 162, 39, 86, 120]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1677)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 77 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1678)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 168 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1679)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .low (![285, 16, 113, 20, 220, 66, 103, 231, 123, 290, 173, 142, 82, 247, 55, 119, 49, 288, 259, 7, 9, 163, 70, 225, 133, 140, 283, 137]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1680)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 240 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1681)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 58 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1682)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 293 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1683)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 193 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1684)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 118 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1685)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 50 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1686)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 105 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1687)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 58 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1688)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 46 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1689)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .low (![198, 289, 113, 71, 42, 141, 185, 51, 99, 202, 53, 28, 126, 151, 57, 53, 28, 125, 155, 262, 28, 74, 213, 28, 69, 28, 53, 94]) }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1690)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 211 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1691)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 81 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1692)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 5]], proof := .tail 153 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1693)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 237 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1694)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 67 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1695)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 271 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1696)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 235 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1697)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 114 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1698)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 61 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1699)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 30 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1700)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 211 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1701)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 81 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1702)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 33 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1703)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 171 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1704)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 5, 1]], proof := .tail 153 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1705)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 5, 6, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![4, 0, 3, 5, 2, 1]], proof := .tail 241 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1706)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 5, 6, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![4, 0, 5, 3, 2, 1]], proof := .tail 106 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1707)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low (![257, 222, 144, 62, 279, 65, 159, 44, 287, 109, 92, 229, 130, 26, 165, 19, 229, 265, 6, 150, 229, 80, 129, 229, 32, 75, 111, 224]) }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1708)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 3, 2]], proof := .tail 101 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1709)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 1, 3, 2]], proof := .tail 64 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1710)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 1, 3, 2]], proof := .tail 72 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1711)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .low (![170, 228, 174, 188, 279, 65, 159, 266, 128, 88, 139, 229, 87, 149, 88, 281, 229, 22, 3, 149, 229, 149, 195, 229, 250, 75, 111, 224]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1712)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 3, 1, 2]], proof := .tail 191 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1713)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 108 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1714)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 148 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1715)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 58 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1716)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 35 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1717)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 37 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1718)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 36 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1719)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 226 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1720)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 108 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1721)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 148 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1722)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 59 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1723)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 242 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1724)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 58 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1725)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 35 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1726)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 2, 1]], proof := .tail 37 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1727)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 234 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1728)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 234 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1729)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 161 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1730)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 63 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1731)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 35 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1732)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 293 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1733)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 193 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1734)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 11 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1735)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 181 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1736)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 294 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1737)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 59 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1738)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 3, 2, 1]], proof := .tail 191 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1739)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 293 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1740)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 193 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1741)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![5, 6, 0, 2, 1, 3], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 58 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1742)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![5, 6, 0, 3, 2, 1], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 271 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1743)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 61 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1744)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 30 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1745)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 171 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1746)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![5, 6, 0, 3, 2, 1], ![4, 6, 0, 3, 2, 1], ![4, 5, 0, 3, 2, 1]], proof := .tail 214 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1747)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 3, 6, 5, 4], ![0, 1, 2, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low (![257, 222, 144, 62, 93, 31, 182, 44, 287, 109, 92, 286, 48, 26, 165, 19, 201, 265, 6, 150, 245, 107, 129, 175, 32, 156, 295, 223]) }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1748)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 1, 6, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 3, 2]], proof := .tail 180 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1749)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 1, 6, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 143 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1750)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 3, 6, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 216 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1751)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![0, 3, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .low (![170, 228, 174, 188, 29, 31, 182, 266, 128, 88, 139, 21, 87, 149, 88, 281, 275, 212, 3, 149, 149, 149, 195, 34, 250, 272, 164, 268]) }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1752)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 3, 1, 2]], proof := .tail 145 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1753)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 89 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1754)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 3, 5, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 91 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1755)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 5 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1756)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 3, 4], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 13 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1757)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 251 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1758)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 1, 3]], proof := .low (![127, 218, 227, 269, 98, 134, 182, 183, 4, 24, 248, 274, 87, 115, 147, 210, 122, 212, 25, 233, 166, 52, 197, 38, 207, 79, 18, 54]) }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1759)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 3, 5, 4], ![0, 6, 1, 2, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 205 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1760)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 1, 5, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 89 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1761)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 3, 5, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 177 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1762)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 3, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 102 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1763)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![0, 6, 3, 1, 5, 4], ![0, 6, 2, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 23 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1764)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 292 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1765)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 3, 4], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 13 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1766)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 2, 1]], proof := .tail 251 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1767)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 243 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1768)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 95 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1769)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 187 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1770)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 256 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1771)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 172 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1772)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 45 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1773)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 146 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1774)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 121 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1775)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 230 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1776)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 206 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1777)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 84 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1778)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 3, 2, 1]], proof := .tail 206 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1779)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 45 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1780)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 146 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1781)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![6, 5, 0, 2, 1, 3], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 5 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1782)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![6, 5, 0, 3, 2, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 158 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1783)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 282 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1784)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 47 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1785)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 154 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1786)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 6, 5, 4], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![0, 6, 5, 4, 2, 1], ![6, 5, 0, 3, 2, 1], ![6, 4, 0, 3, 2, 1], ![5, 4, 0, 3, 2, 1]], proof := .tail 284 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1787)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 261 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1788)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 0, 1, 2]], proof := .tail 169 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1789)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 0, 1, 2]], proof := .tail 219 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1790)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 6, 3, 4, 5], ![0, 2, 6, 3, 4, 5], ![0, 1, 6, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 104 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1791)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1664 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1664 ≤ id.val) (hhigh : id.val < 1792) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1664)) = true := by
  let j : Fin 128 := ⟨id.val - 1664, by omega⟩
  have hsum : 1664 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1664 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard013
