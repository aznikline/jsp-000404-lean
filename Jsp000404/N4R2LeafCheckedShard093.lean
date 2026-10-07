import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard093
open N4R2RowDataReplay

-- Original cycle 09c2fbd2a4b98525759086c5002994ac73e48a5e3c20773218599b37afa544bb; original global index 781.
def localCycle00000 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 0f32e534b6befaf2f5e981639768305e34e2388596b3f0fac4fd7d30a46c3ede; original global index 1213.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 137aff8ecde8798fc78b9b8a3964d477a0a04ce851fe69009ba9eafb42e0d849; original global index 1535.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 34 0, .gapLower 5 1, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 147cb3dcc07746694e132dc139f2c52292f5b97dc59226a4397a08682b349ebb; original global index 1621.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 18856d15c9413df0ec7c762b273fbb511a512762ea17e3a512da2ae04cca6837; original global index 1919.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 2, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 1a43e272c3cb1d5402a36836d5462746378ce7f592dd83a2986e3f0cb645fa3f; original global index 2051.
def localCycle00005 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 3 1, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 1ba7e0c08def4df6c6db57a54d2eadf1c5b4d96bc19c3feea2ab9ed49a2fefff; original global index 2141.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 1e62f3d6245625bb8e03d0f06f0b965e4602ac727cf5162deae9b45451d4f350; original global index 2334.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 241553a299a018cca31db92af6cca9925b667164b823b0b753e019c07fa2a63f; original global index 2765.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 29126f885cd2ac1727fe302f58dfc0f91378c1b0186242278a6cc5945748387c; original global index 3139.
def localCycle00009 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 2f4798706d9c1f078f02e814ba2704762f110ee91d3e2f0b9c712aa38d7bbdc6; original global index 3613.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 371ec405093e73fdb11c0fe3b6dfa77ffc63143cb16536a3a4fc01bde3ca239d; original global index 4229.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 3a5e47b8a837fafc9e3e693e35ff5d34e0094f82cd42cbf38776641832c1fb48; original global index 4508.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 3d08155d3096be81efd9523f7f17b9d49abb06292eb92748c141f5e399dfd945; original global index 4729.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true] }
  origin := ![.triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle 3db8110e03bb76d4cfe7f4b6beaa93e248027d17e728b245e9980e73791024c6; original global index 4780.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 3e0df4bb0d8c38f08c579f66342c7eb312d078f7aaec0adea9c83d38d0b04fe1; original global index 4799.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 3eada455659ac29818345e0d65b53a601b1b439322159a42babe389a281d2a0a; original global index 4847.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 2, .gapLower 2 0]

-- Original cycle 3ff8a4df8740a8e289f3b1db0e1334bad8edca804595f85a837e2e2d2395488e; original global index 4936.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 415864340268c4b4a1eb0a267b3bd3935885134ede91b61b4364bbddd517068e; original global index 5045.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 41ad4392970ded4f6a91933b5310cf2ab9102540f92577388e1e9b2e93ffb5ba; original global index 5066.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 42889a40cb645d41315857ce306aaaef4e72c55e3f0988246c2941caa01247c1; original global index 5125.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 46aaa9b20b7e688ff9849637d2833266a54e09af890b2dc42656d9b0a5064564; original global index 5471.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4844afbede95e33de8b14c1f7aa83ce4449fab02f23fb7f86933d81ae675b79a; original global index 5593.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 4c12c996e71fbd3471e8430fb5c49d734cde636596839341ba1da552bee3606c; original global index 5908.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 4ee240cdf5d50375407e4e321eaf12f2ecae912b0915da6ee87d2c33ac1b41ff; original global index 6128.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5208da9e867dc9f4cd84cefdc188e4713e30bcce1b5ef70782073947c77ce993; original global index 6381.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5a68e1aa6f11879cf4042d511e69e1c03ef986e39a07bcc50bdd55193bef63d5; original global index 7036.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 5aadb8a5a448a7fc2a670d307e546632e667827994bc6a61c55a46fd91861828; original global index 7059.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 5f069e116816eba29b32c806dc943e1f8650b99c94d050a17a4e25f9916c5701; original global index 7399.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 2, .gapLower 2 0]

-- Original cycle 619187bf139163f0151fbc5ed5451d293211049689ab6894d179ef84fe9c6ccc; original global index 7614.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 26 2, .gapLower 2 0]

-- Original cycle 6287dca7abf492316236c746023e9430c952a6d505c6c4a8efdcbe0503e780de; original global index 7687.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 62a548426fd457fb439b13aa62706159e09ac69660b9adb981dbf40f3a427763; original global index 7696.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 656a309fbd2e7cae52b6365259da8b924de4a61878fa6ef25216c44a183e6967; original global index 7889.
def localCycle00032 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 6a2e091bedcd331060af658c73c6dd6fab1ac0cc034a72203874ae6d88895c74; original global index 8261.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 6e56422e6453375178cee3d77720bf20be723121a3fa2e08d58ca8d55f7a7d01; original global index 8564.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 7138f05e6df8c7cda18a91ec97822bf9afd6401a57603d631799eb4d97abd5ee; original global index 8781.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 34 2, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 7841cffedc0c642211e20e73b5c70a6d3f051d0c528ea6cdda082a9c41123ad3; original global index 9296.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7bb721e6c9f2728d1f352b8f45927d51a91c4ca60d8f59d12223e4dd127b942c; original global index 9570.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 7d1a439d12dd8e1ea190944dae4313ef9f7e7701b35e1d8aaf055bc69ec216c0; original global index 9688.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7d1e6199d2357212c9f08bb3aa17dad0a024b3e3513b9505d8c561d866209748; original global index 9693.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 29 2, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 7e125d86481d90b991825470cc91c975a1c76417a6aee9f55d2ece2ad37347e2; original global index 9793.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 8110abd29923a0ea49720f80965df816c1795124e8aa2dd9c6fc0391358097d2; original global index 10016.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 2, .gapLower 2 0]

-- Original cycle 82ef834891bb43b2ffbdea47f9e52e6baa9724c53b6ed3b594314fc19de1158b; original global index 10154.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 0 2, .distance 0 6, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 7 0, .triangle 8 2, .triangle 4 1, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8336c0fd5663eeaea19b346bd1b8e175571704fd9522d33a3b08fdbead05c6a0; original global index 10173.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 88a6190bea46021aefdb866605c3f357d5cebf18dee40a9d8cccb9806fe18689; original global index 10586.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 91a70ed233a8ef4cb085a1f84dbb7947cce38f33045cd30786ba92539f3db4d0; original global index 11288.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 95a3b30d83dde053cd6382f696231d2da403ef726485230b5ded458829425dc2; original global index 11629.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 997c5a52e158ae1b78d1d5e32e8a4db878479ca6996e8115524ba94050f561aa; original global index 11920.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .triangle 29 2, .gapLower 2 0]

-- Original cycle 99d1e5ee3e9d1614a40006b9cec9f73dbb7446e05d8a61a0bbbd0a5046670945; original global index 11941.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .triangle 27 2, .triangle 30 1, .gapLower 2 0]

-- Original cycle 9d9da7de93964290c0d82fdbc690e9151159f8b5263e5587cbd1a56fdae42a1f; original global index 12256.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a0598d0bb58a2bdfb59d5184a9bf9e4c0fe634af94380ca2234e98e824cd0127; original global index 12479.
def localCycle00050 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a0b7878ec98d5b5aad27b6c181d2ab0982f04d29bba001a97d15175f6ffea769; original global index 12504.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1]
    constant := ![0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 9 2, .gapUpper 4 5, .gapLower 5 5, .triangle 26 2, .triangle 17 0, .triangle 0 0]

-- Original cycle a17cff1ffb21f95e25aebd7b3cc87d5e8ab7363a1fc4e4c4c27280a343b85cfd; original global index 12558.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle a4847e8c571cbde84dc81c3db08ab5b74b02a56ba5ff2e4792c5ebbbdea96aa3; original global index 12790.
def localCycle00053 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .triangle 26 2, .gapLower 2 0]

-- Original cycle ab1329f94ee4796852595386a2e3009993323f431ae1063ae938a500b5b3349d; original global index 13326.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .gapLower 4 0]

-- Original cycle abad8dfa585444a63d7e251390be4f127056ca5f5405711463597a600516e488; original global index 13368.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 26 2, .gapLower 2 0]

-- Original cycle ac24a30b2010ed70f59ccabbefa24e5339eff0620c4136fef5013a5f5404426d; original global index 13418.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 0]

-- Original cycle aed08c04ca174e5b7803e7f364d4599cc297ff4ffd2ade1183dc18037f5c8119; original global index 13644.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle b01a0dfe5aaf4cdfe0a7dbf260b29e3bcca7244576e56f16b177820e768a1964; original global index 13749.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .triangle 27 2, .gapLower 2 0]

-- Original cycle b0a2051c6b1a4399d7d507cedd1b3ba72428b5894f242677d40e3c6d24ce2591; original global index 13791.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle b16f8a16dbac2797ae799a9d57d47dc78270bdf694d79787dd5ddeeb4f00a0dc; original global index 13865.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle b40fdd6846b081c8a802c90b33ee4083fc23640877675895d208c242de992b23; original global index 14060.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .gapLower 3 3, .triangle 25 0, .triangle 26 2, .gapLower 2 0]

-- Original cycle b575d880e9c3dedca33cca6b6a633cafa97b0087d429d8d776eeacf8d1f1944b; original global index 14179.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 19 0, .triangle 25 0, .triangle 26 2, .gapLower 2 0]

-- Original cycle b757b83345be233dccd64a6d50545ae46485a66e4460308da85b41128e6ae83e; original global index 14310.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .gapLower 4 1, .corridorLower 2 4]

-- Original cycle b7821f20101305a1077db67e999e56ffae8614f0d7130e2bb738d8571da218e6; original global index 14322.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b848cb3aab107303b3217ab630ffd1b187bfb8fb60d045c22f90d9d198cba1fc; original global index 14379.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b99d8d39729a257cdc513578c0942ee6f05763f40f3204cce0cf7a78bf326f3f; original global index 14484.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle bb317606118f9a9906555275fa49ec25174b9e2065d09d1346fa6c791b974997; original global index 14616.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6]

-- Original cycle bbdc5b33f77795ed2478d223898d9dddef32c06024184c6e9eb430180ce98040; original global index 14673.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle bdd53bb02b4bc414fd281dd10c5cf6c5627afd7e56b033b40a4a0f15a2b20b1a; original global index 14806.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c0ce49831ff6685eb7e0c170168c322bf7dc73329ef10c609f10e34c2ccb4c85; original global index 15053.
def localCycle00070 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 2, .gapLower 2 0]

-- Original cycle c5d9c55c52d0bb2f2d4da6c9ad871f44f4e9f7f51536a76fa978acded787dd01; original global index 15426.
def localCycle00071 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ca3b3d8f12a8295bf4c19e826bb062c46b67b64eb0035fb79f94b791bcd1fa53; original global index 15806.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 21 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle cb8003e3a394e618c15a18bd050fa0497a434878dc0e9ccde3a87496d8f33952; original global index 15900.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .gapLower 4 0]

-- Original cycle cc1b13654d2f285120b650c95ed747158275eefc8f19d1256dd1c35a8546db33; original global index 15953.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle ce89ef64421de4a8a8f3a6664b3bd7e7f50003c88fff4bd369c33f1ca06fc233; original global index 16130.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d32ac6285963cb1178e8e1ef962cdff8334a8431fc535b77a7f633837ac2fe35; original global index 16471.
def localCycle00076 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle d6bdcffd86e2dece6defa18c1650e96ca4c7c1815d5f7b45e5316e5e38ab6694; original global index 16765.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 32 0, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle d797f667c0bc3458393f0f32c9c48cf6374eac90e651a720acc19b2b50ee02f7; original global index 16823.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle dff3b212deae0a9c5882a394d5cf194616184b69df0f08a30fe0a3738ee35f27; original global index 17506.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle e565e64006f477d21c0b0d9c4c8dcbfd6f76efd02cd6f8fa78cddf7079692beb; original global index 17935.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e7c64f97aaedb73b5db672beb0297757a251264fe5b8af8875c8b22347a6c8e8; original global index 18125.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle ea61d6f69599e116afb35819fdb2a476759c9c20c639f231d0571b63313b68e3; original global index 18306.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle f388428468d6a0e915f48fe3c9927e11e91cd23cb81667844fadf4dc38418e16; original global index 19002.
def localCycle00083 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f4d7bc61ad3cd267443e6678191e4f94ac25cf79a0484094f019fefdbfbd5b39; original global index 19085.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 0 1, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f651f3beb36dd8c7b898bfcf169997bff232398061bf4e6b2a816d10c7201993; original global index 19211.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 26 2, .gapLower 2 0]

-- Original cycle fc8b22ee9afd7dddc03f96bb1f19cd6e750c8a1370910e5c03143a0ac6685ac4; original global index 19731.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle feaee9f47587064c2dc91215a5b2fc1bb83eb27fc5eed1078855253d14be8589; original global index 19913.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 1 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

def library : Library := fun id => if id < 44 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 38 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)))) else (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))))) else (if id < 66 then (if id < 55 then (if id < 49 then (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))))) else (if id < 60 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))) else (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))))) else (if id < 77 then (if id < 71 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))))) else (if id < 82 then (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 85 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 1, 0], ![2, 3, 5, 6, 1, 0], ![2, 3, 4, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 75 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11904)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 1, 0], ![2, 3, 5, 6, 1, 0], ![2, 3, 4, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 36 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11905)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 1, 0], ![2, 3, 6, 5, 1, 0], ![2, 3, 6, 4, 1, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 79 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11906)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 1, 0], ![2, 3, 6, 5, 1, 0], ![2, 6, 3, 4, 1, 0], ![2, 5, 3, 4, 1, 0]], proof := .tail 78 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11907)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 1, 0], ![2, 6, 3, 5, 1, 0], ![2, 6, 3, 4, 1, 0], ![2, 5, 4, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11908)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 1, 0], ![2, 3, 6, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 2, 3, 4, 1, 0]], proof := .tail 46 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11909)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 1, 0], ![2, 6, 3, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 2, 4, 3, 1, 0]], proof := .tail 77 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11910)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 1, 0], ![6, 2, 3, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 4 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11911)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 1, 0], ![6, 2, 3, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 70 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11912)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11913)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 34 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11914)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 4, 3, 1, 6, 2], ![5, 4, 3, 0, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 34 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11915)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 4, 3, 6, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 15 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11916)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 1, 6, 0], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 10 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11917)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 8 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11918)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 1, 6, 0], ![2, 5, 3, 1, 6, 0], ![2, 4, 3, 1, 0, 6], ![2, 1, 3, 4, 0, 5]], proof := .tail 76 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11919)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![2, 5, 3, 1, 6, 0], ![2, 4, 3, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 31 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11920)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![2, 5, 3, 6, 1, 0], ![2, 4, 3, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 52 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11921)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 1, 0], ![2, 5, 6, 3, 1, 0], ![2, 4, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 43 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11922)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 1, 6, 0], ![2, 5, 3, 1, 6, 0], ![2, 4, 3, 1, 6, 0], ![2, 1, 3, 4, 5, 0]], proof := .tail 40 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11923)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![2, 5, 3, 1, 6, 0], ![2, 4, 3, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 32 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11924)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![2, 5, 3, 6, 1, 0], ![2, 4, 3, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 52 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11925)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 1, 0], ![2, 5, 6, 3, 1, 0], ![2, 4, 3, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 43 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11926)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![2, 5, 3, 6, 1, 0], ![2, 4, 3, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11927)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 1, 0], ![2, 5, 6, 3, 1, 0], ![2, 4, 3, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11928)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 1, 0], ![2, 5, 6, 3, 1, 0], ![2, 4, 6, 3, 1, 0], ![2, 4, 5, 3, 1, 0]], proof := .tail 74 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11929)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 1, 0], ![2, 6, 5, 3, 1, 0], ![2, 6, 4, 3, 1, 0], ![2, 5, 4, 3, 1, 0]], proof := .tail 2 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11930)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 4, 1, 0], ![2, 6, 5, 3, 1, 0], ![6, 2, 4, 3, 1, 0], ![5, 2, 4, 3, 1, 0]], proof := .tail 35 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11931)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 4, 1, 0], ![6, 2, 5, 3, 1, 0], ![6, 2, 4, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 39 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11932)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 4, 1, 0], ![6, 2, 5, 3, 1, 0], ![6, 2, 4, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 47 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11933)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 7 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11934)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11935)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 4, 3, 1, 6, 2], ![5, 4, 3, 0, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 25 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11936)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 4, 3, 6, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11937)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 1, 6, 0], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 37 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11938)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 72 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11939)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 1, 6, 0], ![5, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 0, 6], ![2, 1, 3, 4, 0, 5]], proof := .tail 22 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11940)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![5, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 69 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11941)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![5, 2, 3, 6, 1, 0], ![4, 2, 3, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 82 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11942)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 2, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 23 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11943)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 25 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11944)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 1, 6, 0], ![5, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 6, 0], ![2, 1, 3, 4, 5, 0]], proof := .tail 33 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11945)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![5, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 26 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11946)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![5, 2, 3, 6, 1, 0], ![4, 2, 3, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 82 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11947)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 2, 3, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 23 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11948)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 25 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11949)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 1, 0], ![5, 2, 3, 6, 1, 0], ![4, 2, 3, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11950)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 2, 3, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11951)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 2, 6, 3, 1, 0], ![2, 4, 5, 3, 1, 0]], proof := .tail 27 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11952)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 87 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11953)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 18 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11954)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 25 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11955)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 1, 0], ![6, 5, 2, 3, 1, 0], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 25 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11956)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 58 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11957)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 1, 0], ![6, 5, 2, 3, 1, 0], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 58 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11958)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11959)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 4, 3, 1, 2, 6], ![5, 4, 3, 0, 6, 2], ![5, 3, 4, 0, 6, 1], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11960)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 4, 3, 1, 6, 2], ![5, 4, 3, 0, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11961)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 4, 3, 6, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11962)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 1, 6, 0], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 3, 0, 4, 5]], proof := .tail 61 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11963)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 4, 6, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 1, 0], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 28 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11964)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 1, 6, 0], ![5, 2, 3, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![2, 1, 3, 4, 0, 5]], proof := .tail 85 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11965)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 1, 0], ![5, 2, 3, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 85 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11966)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 1, 0], ![5, 2, 3, 6, 1, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 29 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11967)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 3, 2, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 55 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11968)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 53 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11969)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 6, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 48 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11970)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 3, 6, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 1, 6, 0], ![5, 2, 3, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![2, 1, 3, 4, 5, 0]], proof := .tail 41 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11971)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 4, 6, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 1, 0], ![5, 2, 3, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 41 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11972)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 1, 0], ![5, 2, 3, 6, 1, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 29 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11973)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 3, 2, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 55 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11974)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 53 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11975)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![5, 6, 4, 3, 0, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 48 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11976)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 1, 0], ![5, 2, 3, 6, 1, 0], ![4, 3, 2, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 56 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11977)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 1, 0], ![5, 2, 6, 3, 1, 0], ![4, 3, 2, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 56 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11978)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 56 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11979)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 56 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11980)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 16 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11981)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 1, 0], ![5, 6, 2, 3, 1, 0], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 16 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11982)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 4, 3, 1, 2], ![6, 5, 4, 3, 0, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 1, 0], ![6, 5, 2, 3, 1, 0], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 16 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11983)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11984)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 73 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11985)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 12 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11986)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 2, 5, 6], ![4, 3, 0, 1, 6, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 9 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11987)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 2, 6, 5], ![4, 3, 0, 1, 6, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 50 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11988)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![4, 3, 1, 2, 6, 5], ![4, 3, 0, 2, 6, 5], ![4, 3, 0, 1, 6, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 50 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11989)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 6, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 5 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11990)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![4, 3, 1, 2, 6, 5], ![4, 3, 0, 6, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 50 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11991)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![4, 3, 1, 6, 2, 5], ![4, 3, 0, 6, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 45 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11992)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 3, 6, 1, 2, 5], ![4, 3, 6, 0, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 83 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11993)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 6, 3, 1, 2, 5], ![4, 3, 6, 0, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 1 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11994)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 6, 3, 1, 2, 5], ![4, 6, 3, 0, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 54 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11995)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 6, 3, 1, 2, 5], ![4, 6, 3, 0, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 67 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11996)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![4, 3, 6, 0, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 71 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11997)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![4, 6, 3, 0, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 54 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11998)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![4, 6, 3, 0, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 51 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 11999)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 68 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12000)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 68 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12001)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 2, 5], ![6, 4, 3, 0, 1, 5], ![4, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12002)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 2, 5], ![6, 4, 3, 0, 1, 5], ![6, 4, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 13 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12003)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 3 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12004)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 86 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12005)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 64 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12006)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 66 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12007)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 86 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12008)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 19 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12009)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 6, 5, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 44 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12010)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![4, 3, 1, 2, 5, 6], ![4, 3, 0, 6, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 84 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12011)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 3, 1, 2, 6, 5], ![4, 3, 0, 6, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 66 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12012)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![4, 3, 1, 6, 2, 5], ![4, 3, 0, 6, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 42 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12013)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![4, 3, 6, 1, 2, 5], ![4, 3, 6, 0, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 0, 3, 4]], proof := .tail 80 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12014)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 6, 3, 1, 2, 5], ![4, 3, 6, 0, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 21 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12015)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 6, 3, 1, 2, 5], ![4, 6, 3, 0, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 0 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12016)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 6, 3, 1, 2, 5], ![4, 6, 3, 0, 5, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 6 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12017)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![4, 3, 6, 0, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 17 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12018)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![4, 6, 3, 0, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 0 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12019)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![4, 6, 3, 0, 5, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 59 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12020)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 5, 2], ![4, 3, 6, 0, 5, 1], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 20 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12021)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 5, 2], ![4, 6, 3, 0, 5, 1], ![4, 6, 2, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 20 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12022)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 5, 2], ![6, 4, 3, 0, 5, 1], ![4, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 24 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12023)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 4, 3, 1, 2, 5], ![6, 4, 3, 0, 5, 2], ![6, 4, 3, 0, 5, 1], ![6, 4, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 0, 2, 1, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12024)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 14 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12025)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 65 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12026)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 5, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 38 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12027)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 5, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![2, 0, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 66 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12028)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 5, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![2, 0, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 86 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12029)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 5, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 0, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 19 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12030)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 3, 1, 5, 2, 6], ![4, 3, 0, 6, 5, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![2, 0, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 66 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 12031)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (11904 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 11904 ≤ id.val) (hhigh : id.val < 12032) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 11904)) = true := by
  let j : Fin 128 := ⟨id.val - 11904, by omega⟩
  have hsum : 11904 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (11904 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard093
