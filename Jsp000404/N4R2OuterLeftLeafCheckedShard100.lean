import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard100
open N4R2OuterLeftReplay

-- Cycle fingerprint 005a5663f9afdd769bbaf3681c0be281a6f7e18811ce593dbbc91bcf97f862b2.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![-1, -1, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 13 0, .gapLower 0 4, .triangle 10 0, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint 05d23b3e91f7b55b20e37badd2e59869039b74bf43f5836b2361d42a08eb5177.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 08620e9de650a01bcfe6bd01ca7a2833291abe2fecdd22eb33943e64400e585c.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 2, .triangle 12 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 09c6500d0248f34b693bb77f284b5f347215f7be5af2cd1056f29a527ce558cd.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint 0d541cf2a74a2fa6cc4f94137bcec7e7739b1465a34c6cdec5bdb45ae259c8d3.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 0ea438e66f0698bf38541fab53b8e0b11fd9435b4d111f1cfac4c3c1fd7ac092.
def localCycle00005 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 0f9312e596aa08bdcf752aa3d1f16a30e61103858abcd999bbbc9443c5cb863f.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 13535f99b105865a8ff3e765a76cb48427542d979ee7df6d6b8854981fba1515.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 1394b105fdbbc1cdcb82d2c56a3873339e28e8baff651a3cff3c734da795cf19.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 1688dbca4372d0177b2d8fd9f1fe01d017749d7792d51ca16fb9d88557fb6ba9.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 5 1]

-- Cycle fingerprint 1693f56d0310cb6fc1aaea48a783d7c997f60ce5ad871d8acda804da596df7ed.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1dbfe66f9a8a5314850ed079a6948b4d0d3b91d638ef0d6a7bef8a0344304ba0.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2130f8febb69c431552037f800103aecfc88993348c97dd2e26a9e8e6da7cb26.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 28ea14d068fe521e94ceb94e26ba38ed58bc901196315c02238a548b40e99ab5.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2b7194951745b95c7113c20e554fa0aa121abf4bd855c02587bfcb05e4de9938.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 2bd313f4ea5c2302cd3b77740e4982c4340366927a5de9a2d08b80c859daf41e.
def localCycle00015 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3089676be77197ae17799fa3665b2ba79fee2a9d3a72bd4bd56c30de24d4eac5.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3]
    constant := ![-1, 0, -1, -1, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 30caa2d623dd4ce5893c9a1523ec8478ffb42a0320e2984bd8921b4e713a72e1.
def localCycle00017 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 34edb5a98fd32973fa8916eba726b20afbdc31b5d1b956fa841842d7a12c4157.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 35a2467ccf8af853d717d881a8348c2cd3451956997bc4789d7178a4ccb4b6eb.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 370728bd35eda36a700f60eccb5b8c2962c7270749d01a874b139b8ece9fe302.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3a282809ff03f0aa279cd6ee760f30e6d8a2d056d6e4a829347c0268d41a44f5.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 3bfe57b3065688ca7ad1d633ed776e5125200381dc06de58bf29b0554aa5f4df.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 33 1, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 40545932fa7aa145e1e42b7fa600c16b40f51c3eb25a2bbddf8361857b0b1fbe.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint 422971613005ef0bd29b9ef45e224d4eeb9908a51a1d3bbbe642fd875dc6b1ec.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 4f96300051eea6f8881a6be3f0277d1999ed95563ab16cb35a612b36ad89b2ee.
def localCycle00025 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 540e3764c3b9ab6dee04bcce4531d0e07c756ea6d139692eaa9744abd2bf8eed.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 575b56ef66938f11ba5f1e3782346af551a312ad433c81f06c537f5d69cd43e2.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5cf55d992eb4818302ae72b383e2c1da3704eb928b82034fcbdd1f6088c7e83c.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 5d3193fa882a42fe198d0f71bcd86b00dc8ba90969d4b5a5cd842027c000ec1d.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 61185bf0ac6334614e05c08441a07c64a1f937af577244b1b3620e10da0c67e7.
def localCycle00030 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 64d2ca5c4be8f5d3e08dd3b73e61bd7565fb95aa3decf1fe9a17fc8a66a20bba.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 695bcded1542d87c26f9537ca5f63150e05ec31cea0fc001a936fde9248bb7a3.
def localCycle00032 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6b5d3998cf5b0c6f5a3719daa42448e17af3e178fa8d75453046a61dff82d450.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 6bb4459f83adb626948bbc2d0d33ef0465144e90956c1b282b03a2a09de9a78c.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6]
    constant := ![-1, 3, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 3 6, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .gapLower 0 4, .triangle 11 0]

-- Cycle fingerprint 6ca31928e711c81a1bf7e589bd5d88cfda78c98cb5f76f165d21fb1eaff26bc3.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .corridorLower 3 6]

-- Cycle fingerprint 7549d5c400d5eac0bb30f0cce2c73326d425ba54a48809fbfa28f424b8918018.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7648eba78b1a0f189348e094cdcd15c40aac02e97f0b2f93b981cb0df622744e.
def localCycle00037 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 778feb19bafa22675d519268dcdbfff8256fc5bb3d8816626fdc26acadf030d0.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 783c7f2534cf08aa2f71c6dd246efc833ca2e1953cca9e80be11234dccc17338.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7971330c902863125818df70a680cf36ecfd88cba861655c142a3b71ca263930.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 79bacc2c7797dafac7793e1bfa791fd6b12d64c47a7bd111e49d40b45c94762b.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint 7d068142efebada23cc7c5871559fef3d29b0af2a3c357a338a484a9b98cb45d.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 84cb98fceaed0995746b442e538f9e44c030bc32a41a57d217531e9f52cb6020.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 867a75fc9adf6c032a482a02f03a5712fd247c4eb470c100f5ff9df3719d36b1.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 9 1, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 868199230ba7493a742afa5fb89ce748c8170b7146d20777b51bac2d878ff2b7.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 8718f4943e4b959787f25eca66029b909b749c1d9137c7cabf343753e7236f0d.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8b2376d4ba2a02a34af6fb195813615760a7142361faa14cca137c5a0c96cd28.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 6 1]

-- Cycle fingerprint 8fff767ca2c36ee88dcb897079da5497f078e69b31e54595c7eca599d40bb434.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 93fce1e9aaa66578333bdf97a3d35a5107cceefba31042ea40875d8c17f9bbc2.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 9eed53d94b1badbc3e26f193d50085a0107a8a30351cfe208aa5b8227480b540.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 6, .theta 6, .theta 5, .distance 2 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 6]
    constant := ![-2, 0, 3, 0, -1, -1, 0]
    coefficient := ![-1, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true] }
  origin := ![.gapUpper 6 6, .thetaNext 5, .corridorUpper 2 5, .triangle 26 1, .triangle 20 0, .triangle 1 0, .triangle 4 2]

-- Cycle fingerprint 9f3d443bfb580ef4c18f290b1c63e2969ee2fe5ba9b7aaa835f0a0c3fe3f7b1b.
def localCycle00051 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a0162ef62fc700988dfcdc97ff4feeb2b22d7bfdf91c351263d60eb75dc2b54d.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint a837fbf9e5ad206fc0f00fb3ea308162b80d0d272a251a7ef1614ccfe9739bbc.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint b0da1277a8e02bae3b52eeb671ce79f9b7d96007acf2c2ed4dd013bce018612f.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 3 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b108c3dc765b75f119678113ae1a49bdbb9471fcf087e906427e42d30940281b.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 20 0, .triangle 10 0, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b23e7fa290e3e7db60a02fe417a9f0f15b7c402c7531de2113cc8926365e9239.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .gapLower 3 0]

-- Cycle fingerprint b48ec7823cbc1ffea24fd5b2d3d461d116a358564174ff35bb7a6b7e3e8daa13.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint b5ae5327e43f5ffa085b1dd4ec0e92c2dc8a11f79099d99b76b5219c3d501957.
def localCycle00058 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6]
    constant := ![0, 0, -1, 0, 0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 4, .triangle 1 0, .triangle 4 0, .triangle 21 1]

-- Cycle fingerprint bae473f0cf77d3643d49a656866b90150b7987d499a69e39ba9821ab8a453bd9.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint bd16864072b324f7e0d12fa786eedfca7ca37f89e9f3c90341089ca7c594c9f2.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint c07e6f6da97bf48b137c419b755f778f3509ff17d29cc683a7c372e2856cba31.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c62a74f8111a44ab213b58d017abbad7d88f2eec4155cf42762fdc44c590241f.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint c7134f82acd4f8da5993fa736c42358ac436f582070f9db970080dbcb228e00f.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 20 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4]

-- Cycle fingerprint d224c1bbb2dd63944e32b6de8b4763b79f5e6700a847d4ad0bf775dfc20486c2.
def localCycle00064 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint d24416fb94192f46500c6018633c96bc02041570713c5d20167f03edcf609b6d.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d2d5ac11f74ffbb35c6c6b218fe82d9fae2c1ca765097be3e38e8429e91a1214.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint d450811db7272852f8c84489cc38392f38a5fc96f9437df75e2a1e3baa01e93a.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d5947321693a0c0dd435c6fcdd2538ccba32935dd28b424f827131062857e3f1.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 6 1]

-- Cycle fingerprint d601bbe45c14617d579b4a33b0bb1b7ae1e7bbc6696af8b6a3411a4f791a4411.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 5 1]

-- Cycle fingerprint d9f00a0ba429cba9f80d2cb282f03609f18f32facf8a96a78fe0b4186dfb8caf.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint e361bbb0c425689f19ed9d0cb06f5ab426e438a596bf2f175379cafaa2b4a807.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 18 2, .triangle 21 1, .corridorLower 3 6]

-- Cycle fingerprint e3c9d8521b4bdf48fc4f334c76c2b0828b8dfbabdd4f4082394e20df626401d7.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint e7ca72b3eda7b3992b36252211a665ddba39127f55c0ab24e37daeea68854a90.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint f23cf7509cc4228cf9608e5c7665de615fc877da28abd2c1511abc1c637fe590.
def localCycle00074 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 1 1, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f44c7f6aacb9d052dce7eee8b5c080e8babb66fd59748fa5ba29c5c7877d1c54.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f57e0f5013735a252e3c6f54e6cfaee4b1323ab1038511ad466cf22851776c8c.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Cycle fingerprint f8fecb9f530f0e5e83b08fde72bb51691483b80f442c6ac73dd6ea369a5c8d01.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

def library : Library := fun id => if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 58 then (if id < 48 then (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 53 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))))) else (if id < 68 then (if id < 63 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 4 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12800)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 3, 4, 5], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 34 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12801)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 3, 4, 5], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 58 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12802)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 3, 4, 5], ![1, 6, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 50 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12803)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 3, 4, 5], ![6, 1, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 50 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12804)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 4, 3, 6], ![0, 1, 5, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12805)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 18 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12806)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 1, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 46 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12807)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 29 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12808)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 1, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 61 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12809)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 73 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12810)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 51 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12811)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 22 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12812)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 73 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12813)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 74 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12814)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 74 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12815)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 1, 3, 2]], proof := .tail 64 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12816)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 33 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12817)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 1, 3, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 59 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12818)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 1, 3, 2]], proof := .tail 19 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12819)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 37 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12820)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 4 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12821)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 4 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12822)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 4 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12823)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 35 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12824)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 71 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12825)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 77 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12826)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12827)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 2, 6], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 32 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12828)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 23 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12829)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 63 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12830)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 4, 6, 2], ![0, 5, 1, 3, 6, 2], ![0, 4, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 68 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12831)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 1, 6, 3, 2], ![0, 4, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 63 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12832)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 5 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12833)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 47 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12834)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 15 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12835)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 15 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12836)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 43 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12837)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 5, 6, 1, 3, 2], ![0, 4, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 56 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12838)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 1, 3, 4, 5, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![0, 6, 4, 3, 1, 2], ![0, 5, 4, 3, 1, 2]], proof := .tail 17 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12839)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 1, 3, 4, 6, 5], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![0, 6, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 0, 4, 3, 1, 2]], proof := .tail 75 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12840)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 1, 3, 6, 4, 5], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 45 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12841)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 1, 6, 3, 4, 5], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 45 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12842)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 6, 1, 3, 4, 5], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 41 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12843)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 41 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12844)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 2, 1, 3, 4, 5], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 41 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12845)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 4, 3, 6], ![0, 1, 5, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12846)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 4, 6, 3], ![0, 1, 5, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 14 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12847)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 46 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12848)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 1, 3, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 28 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12849)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 61 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12850)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 1, 3, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 28 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12851)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 1, 6, 3, 2], ![0, 1, 4, 5, 3, 2]], proof := .tail 12 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12852)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 1, 3, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 28 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12853)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 1, 3, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 28 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12854)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 1, 6, 3, 2], ![0, 4, 1, 5, 3, 2]], proof := .tail 12 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12855)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 1, 3, 2]], proof := .tail 12 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12856)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 24 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12857)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 5, 6, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 3, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 22 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12858)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 5, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 3, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 73 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12859)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 5, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 1, 6, 3, 2], ![4, 0, 1, 5, 3, 2]], proof := .tail 16 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12860)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 1, 3, 2]], proof := .tail 20 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12861)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 1, 3, 2]], proof := .tail 20 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12862)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 3, 6, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 1, 3, 2]], proof := .tail 19 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12863)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 1, 3, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 36 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12864)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 36 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12865)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 38 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12866)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 48 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12867)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 76 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12868)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 10 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12869)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 10 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12870)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 1, 3, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12871)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 53 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12872)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 3, 5, 4], ![1, 6, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 35 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12873)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 3, 5, 4], ![6, 1, 0, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 1, 3, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 77 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12874)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12875)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 31 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12876)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 3, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 23 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12877)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 3, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 55 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12878)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 3, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 9 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12879)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 3, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 55 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12880)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 28 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12881)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 28 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12882)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 67 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12883)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 67 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12884)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 43 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12885)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 1, 3, 5, 4, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![0, 4, 5, 3, 1, 2]], proof := .tail 11 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12886)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 1 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12887)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 69 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12888)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 42 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12889)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 42 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12890)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 3, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 43 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12891)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 1, 3, 5, 6, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 0, 6, 3, 1, 2], ![4, 0, 5, 3, 1, 2]], proof := .tail 11 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12892)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 0, 3, 1, 2]], proof := .tail 11 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12893)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 1, 3, 6, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![0, 6, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 0, 3, 1, 2]], proof := .tail 2 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12894)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 26 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12895)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 1, 6, 3, 5, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 60 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12896)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 26 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12897)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12898)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 0, 3, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 26 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12899)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 6, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 60 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12900)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 5, 3, 4], ![1, 6, 0, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 41 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12901)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 5, 3, 4], ![6, 1, 0, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 41 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12902)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 4, 3, 6], ![5, 0, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12903)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 4, 6, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 21 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12904)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 7 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12905)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 0 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12906)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 65 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12907)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 44 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12908)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 62 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12909)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 4, 6], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 4, 3, 5, 2]], proof := .tail 0 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12910)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 1, 3, 5, 2]], proof := .tail 65 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12911)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 44 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12912)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 40 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12913)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 1, 3, 2, 5]], proof := .tail 70 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12914)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 3, 6, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 1, 6, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 1, 3, 5, 2]], proof := .tail 49 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12915)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 66 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12916)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 66 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12917)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 40 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12918)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 5, 6, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 3 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12919)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 5, 6, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 3 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12920)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 43 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12921)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 8 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12922)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 39 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12923)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 57 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12924)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 13 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12925)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![5, 6, 0, 1, 3, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 39 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12926)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 3, 4], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 1, 4, 2], ![6, 5, 0, 1, 3, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 72 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12927)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (12800 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 12800 ≤ id.val) (hhigh : id.val < 12928) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 12800)) = true := by
  let j : Fin 128 := ⟨id.val - 12800, by omega⟩
  have hsum : 12800 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (12800 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard100
