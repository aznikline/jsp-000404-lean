import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard128
open N4R2RowDataReplay

-- Original cycle 006dcab8a01bd0c39e209bc28717dacc21e70220bd89fbecdfad62e00ba0be18; original global index 37.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 0118e80104e090ec02e26637fa0d135c4e3cfe55d19f7384610b679f50d51eb5; original global index 96.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 0143c6662819ca592d6241eb7192611361eeadaca8a04f1c9d6db4ed6d8e49fb; original global index 109.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 01af05dc6f76169f5ac988be262df9559e6d8ef94e2cedd43f8fe5bb1bd85d9f; original global index 138.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 028ac5a9078985b7628e87d98b9551b560595af7236971b85f8aa148816d1462; original global index 198.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 029f2d48007e2173174c7b817690a23d2b36776f97201de4841bf5ec0a173b98; original global index 204.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 03935bc86337566f7d32c5ff433931446070657a4f34329178870ee6feb9d037; original global index 288.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0615c28e16322666ab37b50794d556f0dedba93acaf1bf091ea1916d51a353e0; original global index 503.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2]
    constant := ![4, 0, -2, -2, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3]

-- Original cycle 06bf8d79ee3643eac2873f40357a04ad5eca36501303e041b461dcea566482e1; original global index 554.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 06c3012b8534a627350cd2da0029c13a0f67b550813c960822d666af9b64eef3; original global index 555.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle 070e9a16a7e72fe21ded774a7cda4c71aacdd13005fa17c40c9e550c1574f4a3; original global index 578.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 073eec2dc4fbdf6d35ffbd2f5cfaf33537cfe0d2628ea1ee36ec0ce4f0380cbd; original global index 596.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 0834bcb07ae67b42fc6fdd38b5e89fafa12f52033c2a72b2439bbcfb537b81ec; original global index 656.
def localCycle00012 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 27 1]

-- Original cycle 0a16ca50c753fd53877dc2825c9bc875223dc809acd4b4e25125692f18b5abf1; original global index 813.
def localCycle00013 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 11 2, .triangle 13 1]

-- Original cycle 0ae9fe8b7247d50bf771f9a04a1b17e37b532ab2cb3ab21e3010dd295e645ad0; original global index 873.
def localCycle00014 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 2, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00015 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0bbd77fc2f26c77308049ab53d426eca9af605418a721e2451ceda527e0723c3; original global index 937.
def localCycle00016 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 0bc7d7bd584aea592d1aa699b7d84d73a419c49e6902fc243ba0dd2e5bc189a9; original global index 939.
def localCycle00017 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0ccdab088c5038e8d2a050b5a208a5b1fef9a7d1fef43940d22c7f387679cfbf; original global index 1014.
def localCycle00018 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 29 1]

-- Original cycle 0cf28ce60a6e362b47b8010c7c0bffbdc3871882c9a39e49644a116208bacc47; original global index 1020.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0ea29633a3a2fd0bba1905c215b049014d2ee17610df510cbf4a3481ef5f7ab7; original global index 1156.
def localCycle00020 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 4 6, .distance 2 6, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 29 1]

-- Original cycle 0ec4e83fd5ce31c7b25da4a69acf0cf5659e146e33aba5733d871def85e6e1d1; original global index 1168.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0f23c63acbaeb5263adab35cc33b6ae90cdb7370550aef0f2d7f37a2e3de8c65; original global index 1207.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 103cb625db53e4e2282479cca7d2e34c38349654ffcda0035e01a72bc5dd2f7a; original global index 1306.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 113e244e5c1d29302933907bc476674e33bf39a882a88f85d453eda9e1a303b0; original global index 1368.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1]

-- Original cycle 126dd5e171be5a89751143b0d3d993122ecbb04274a54f7160d7fd6111218802; original global index 1462.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 130d2668deaba6ff652d0d0fe5f6e5fb8fcff7e5f1318490eca0c4aeeb7cf849; original global index 1506.
def localCycle00026 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 11 1]

-- Original cycle 137a7567a3b6b10711ce34983841663161b8bd8ede920e24916e2da9e1535753; original global index 1533.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 13ac460a616e5025dab2bfae0da114498a3ca87b6f3ebff4c781fb97a25505cd; original global index 1555.
def localCycle00028 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .triangle 21 2, .gapUpper 1 4]

-- Original cycle 13b596423420f17fa5d02277b96ca291563c181a3d70a74d30f0ba945b122a2e; original global index 1560.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 4, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 145816f482a42eb28b3e599556cb91542591be21d51c1e4bc8aec2663872d8f8; original global index 1605.
def localCycle00030 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 145d6d04df267934419adc9884323f322f67cfe5783821c9e7d4860c73eeb1f2; original global index 1609.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 14ac65431601b8beddd6ccc04ab882e5828ec24674521e5f58bad8e7a76ad738; original global index 1641.
def localCycle00032 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1]

-- Original cycle 14d79188095b3008232d7aa141db522148dd7753c8acaba6ef1c7273af03689f; original global index 1653.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 1502b6f81a146a760a7158f140ca4304b16ca63688b9653b7e47e9f3a1c4cbae; original global index 1666.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 156c5288a5279dc01f9dc8d8d2e6915a37f293a841c42eb3d04af22e28af8f53; original global index 1697.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 1963787b676a0e75f0d5dda86e9891794b64fd96cc2b1110b35e3c7beb7fa4da; original global index 1983.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1b6559d59a417c72978b83307f9f5ab7f829c5dee641744742356420fff2ef2b; original global index 2123.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1cd63f6b72b6d8cbb84d2a6e5b5d88ab3e6065f967f21bf60844941c0c912bd2; original global index 2218.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1d9686c74357a84c7e36298d22f6eb7f1f6f874c7f662720879275ebb81e90bf; original global index 2276.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 1f69d35e2c4c52c222a89d78e1fd92a8b6a2e7712fdef3f7864755f6fca145c3; original global index 2411.
def localCycle00040 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 4 2, .triangle 8 1]

-- Original cycle 1f98ced88de90cdd19fe6759d96c03d2599d53db02fc7ec3813a5fe7638e3803; original global index 2430.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 212394d54c6da81e6ae2126d9189b8bd73084e73ce2f7a8cb4f2ecf675c40899; original global index 2539.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 212f383e6d286250bc96df42e8e0e5c1bba86fd24e47090bc73caca3de8af266; original global index 2543.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 221bc3ccfbc7128c2b6a2c0202bda1923cf4ce58f8193283cb8586f82a3830e9; original global index 2612.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 22996a966166603f989f71e6786f7820d2c5f5978b2d5cbb344710b5abc8f5c6; original global index 2646.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![4, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 4 0]

-- Original cycle 2482647074acc7062952be3814b7ce43d63f5d760bb8c290426256a190420c0e; original global index 2800.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 2568a0724a433a74a9ab8c55445d4caa7bac4bfab8210f6507f6cf5c38d5061c; original global index 2878.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 2665ed042edba6016e1e85f9a1252e9774b8c7604e014a5f2af2a9a61d936847; original global index 2947.
def localCycle00048 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 26c11aade3f78e412008a1126096c9350ac872f1657fcfdf47809817cf71c177; original global index 2970.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -3, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle 26d821ecc2dec878f21163068cdc83c2653967658e7bdd48054637d6ca300df6; original global index 2974.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle 27f02079afb8d8e40ebdd0b8b4d067f6303e63f8d2b3c14f0cce6e1a06d558ab; original global index 3056.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 284a51ff6e7e87e937f1aa3f95df91bca25aec721d487d4af02d28df581c3fde; original global index 3088.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .gapLower 4 0]

-- Original cycle 28a974669aa912301eeb1526659790d58d49f3b07c32e5e73fa3ae2f5417339b; original global index 3112.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 292a64be506d11616c2018e5d23d2f543423dacb7b48a52561e81fd110f64d8d; original global index 3142.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 2b3a524ad54e90e3a5e31f9a8dba8c8dd754432ca1fe49bcc077373d917a9755; original global index 3301.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle 2bdbe2765c51e7efdf8869aff44eb05c61b98d4276b08c5dd677bc6334a7669b; original global index 3356.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 2d080be512d8d23db6205a7cb89eb007ab01be83b366d58b74d77ac44af54038; original global index 3439.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2dae6a68d65cada2311ba746667ffb5f73c5cf0f20ffdf36ee8bb339f2a5b802; original global index 3487.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 2e1a27f271e29ceb9fc6a8d21d29fa67fe92a44dc63a84a12af385d89c55ce1b; original global index 3522.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 3075ee2af60f21abedf51a7825373af0ccc6cde2c21c1c4acc89c872901242b2; original global index 3689.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 30c287162e803911857e0994338857f2ab686124b7f3d8d083152d63b8da1cd1; original global index 3716.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 310e1e59934231519148b4069557484502711c5e4966f4474fc211bf5248ea2c; original global index 3737.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 1, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 31356c7ac3b0970f891907dbf1aa5ef631af4ea9fa871af71ad73160383ad079; original global index 3753.
def localCycle00063 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 3192a7dac4ba315cdf07204b2e2f24d7f72849c2284cf717760cd91523b26b93; original global index 3784.
def localCycle00064 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 32223b4208cbe7c5e05e2d89187aaa28ec3179c922e37eef57b4a9ae81f9e16c; original global index 3828.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 32a14cc1020b3290d7bbcfcf20b1817e48c7c213a92ba46bb1cc736acc8b7927; original global index 3873.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 334c1ae8746b1121178556eea20ef6b5e3c0e0e7591de01e6d7c116fe285b16f; original global index 3925.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 36050ed86f902da8ec49c2f33cd6d515018a975a4ab37b9bfc6021d005acc4f9; original global index 4147.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 380a581c8e530b417bbdcbaf07dc363fa4509c6884555e30d253f2eecc8a5704; original global index 4301.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 387226af045d056ad99f42909453d80cae6dd6726e21e151865b460e0396064e; original global index 4344.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 388da610600a819ccf40ddf49849f58a10b1175fde0a6e038e68e92fd5754d38; original global index 4352.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 3a222926778fce2606e52c333b1b315d8279e08d84e5588abcf41a67fb47c6e4; original global index 4487.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 0 2, .gapUpper 2 4, .gapLower 6 3, .triangle 4 0]

-- Original cycle 3b06ad2d86b9d10a5cf79e675dc3fc0a863f3a47067e510c14dd03cece0760c8; original global index 4559.
def localCycle00073 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 2 6, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 27 1]

-- Original cycle 3dc55e1dcd3f1f2b9316350e702e64a65f7953465e3260943991d81e955c1af1; original global index 4782.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 3fc02b5ed57cb5e9cb0d12086cb1b17dd219bb239bbd949c825df3be4d80b530; original global index 4923.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 40fa3b00b7dada6743aee53cc312443dc701f38c385a166357449bf955dcfff5; original global index 5019.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 43da90c4b36b98be7f1e17f27cf37a45d1e4d752cf5ea9a6d8aa40509d7ab6ca; original global index 5252.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 440a136b2331bac47f0f087a9ca769e90b0dd078f909cfcf294928e01f34143d; original global index 5266.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 44909177a68273caa9ff53c8753564e9265dcb6d92c47d14ae26327eaafdc8ba; original global index 5307.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 1, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 4800a1b402bc58d736e91f13e4e63df430427f6230b6941c2bc09b41cb62c48c; original global index 5575.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 48fc73cc27e66bad4cde77b320fc62cfe32a7e0d21a5c8a8ef35b7f1fc87676b; original global index 5651.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 48ffc50b60592151472df213e021e88905949711176433b59826428768f94a43; original global index 5653.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4a3e9cbb97d3ebdd3c6b24c48761abd611b058846750a4bc10b14e91308e575b; original global index 5758.
def localCycle00083 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 11 0, .gapLower 6 2, .triangle 24 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle 4a5b13cde2d032322aa6dd9f37c4250df3822d419f3116d0d82c7d17f645c572; original global index 5768.
def localCycle00084 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 4b5e8a36d5251fade1a3012390ea700792e30bf15117fad55e61c09a3fc402e4; original global index 5839.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4be708d78752928b2e859696a1ed313907adedecd35c458d0b20852c25643657; original global index 5895.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 4c38aba49f806e8b74f43a6278252100dc3c96951c5d2101b1bc4009ad14121e; original global index 5915.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4cd4803e861604ce99f46113200009d9e2a2f502181891edab1988c6a2034800; original global index 5966.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle 4e1480439ea5c99dd210c85ede6ff36bfe536f609a27f4d7084bc328de6e0e4a; original global index 6061.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4e271dcb2c818b4903b21b15f39e3435e6aea19d5ff4c052db63e7129dafb92d; original global index 6066.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 4e2ab306ca8acd803e2f1b0637085d71e6c1cd33629f2059e22d2fe731445e4a; original global index 6067.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4e50fb975c6c5cd2b0a2721d398cc490e7e7feb86a53e0815591bcea3a9708c9; original global index 6081.
def localCycle00092 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4eaa9b513809b85b94e81d0c68f84e6caaf12587c7f75ce80545b6c1a2ba8d43; original global index 6110.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 4f5b875a1284a609c3f4a3b8b555f849c49838b343d3a38cef56adc625199839; original global index 6168.
def localCycle00094 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 13 1]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00095 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 50635b019519dcb09d91f06c73530c077c339fe13249549e15d24f72454bbbcb; original global index 6239.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 50e208f4ace704c82e9804eb4682af6e2e8f67b5b4fc41a70e1e6acfa18d8884; original global index 6281.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 23 2, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle 5181cd31931987ec299b38248aa7329924ef67c918f0c2aefbeadc1e058e56e5; original global index 6341.
def localCycle00098 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 53a2c3e08345cb799c2d432fd02fbbce13f90d0dbdc046932e4cfea3814ccd80; original global index 6500.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 53f632116fb63e8837f13ade08f6ff477c35fde887ce06fad4e7530e6341fd3f; original global index 6514.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 55953e6747d1639bc27d1a95700ca665565e2a881e72f8729cc373795677329b; original global index 6634.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 562e1938ac46805bbffa0cc0ac5633076ab43d67d5e1868d1af2baafd5f2b2bc; original global index 6684.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle 56443c853aba9939d749690377acf12b68a5cda9a36f4241be769f0398230e4a; original global index 6690.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .triangle 4 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle 565e581964b9b15891f4a4c05f8aa7e6121d7df404dff9bb6c164b6778e88325; original global index 6696.
def localCycle00104 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .triangle 23 2, .gapUpper 1 4]

-- Original cycle 5698f710c407e57a39ec442ce22554a560e6794776afedba66ecc16bf9c25e54; original global index 6714.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, 0, -2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 5741b8513d0fad2cd330f6e0b815ed957a94fc069cc3657c55955a27b5bb330e; original global index 6761.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 57e54aba3ae874d2a70288162aece22faecd40bf58b177634a8fcaefafdb995e; original global index 6821.
def localCycle00107 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .triangle 21 2, .gapUpper 1 4]

-- Original cycle 597136bdec5fa5bd7960f2813914e99a6e97219018de315cf63886160ccb9b8e; original global index 6948.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 59f03053b9d60a39b7dbb9589d4de7f29e8b05e071bdc304c9d4441db75f2435; original global index 7000.
def localCycle00109 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 5a2ca51b40dc3d457cd54845df16b3bf3f5f33e4ed36001a56c80019b77e2d28; original global index 7017.
def localCycle00110 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5acda26beb4a101904bdb5f433bfe3076301c7db29dcdd1a47a5fd0abaadabdf; original global index 7071.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 5c4773606b0019e170b5cf096e76c7bb11fd21804d64de341ee1e1a7700c35ff; original global index 7187.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5df4c8c6abb3a5042461d452a2fdbbe5798664111de428039fd94329ce710571; original global index 7308.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5dff7e70a40eefc34eeb38c99f5b5500638c23491d23e8328d77fa0d0eb69125; original global index 7310.
def localCycle00114 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 2 6, .distance 4 6, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 29 2, .gapLower 6 4, .gapUpper 4 3]

-- Original cycle 5ff05305996a5272f664ebba869388096ea60361a984acd2257724c3e5b2dfd5; original global index 7481.
def localCycle00115 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 617c89ff5ea88e921c9d88e9a0d600416e617298dbe146ed0cb4f5e6faf3996d; original global index 7603.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 62813c47ce70505a25184a8d12407fbe5f242e27394ee1d7879dea2e1a26ee34; original global index 7686.
def localCycle00118 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 62910ff18385d3ffa206da262ee8b2db0a6d42f05cbfe54b0ffebfb12b3f6857; original global index 7691.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 62deee0c598a69d190a037ff4185e498e7e3a5900f2cb877f965ed08b8e010dc; original global index 7715.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 6311e3c4c9051bffa6cdcc368301edbcedbbdd4783ae16c8f622b3bb7b1ef095; original global index 7724.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 63885fd5b9f32b378627b95221ee7b7218c4cd4691eaad89271a8d18acef7c48; original global index 7764.
def localCycle00122 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 649d1b6128b47ca7afa426cad0c49bb7470e58d93ae1beb99a3e7175cb13068f; original global index 7839.
def localCycle00123 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 652172eb6ed5f40aaa0e6b0105ac9f67f7b5098e54c8c1fe8d6c0f23d86fa99d; original global index 7869.
def localCycle00124 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 2, .gapUpper 3 4, .gapLower 6 4, .triangle 8 0]

-- Original cycle 67464604234e4c9bcb65d9dec794534d9fdc3ecb3704d4d1b655a1b19f7dd7d4; original global index 8030.
def localCycle00125 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![-1, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 13 0, .gapLower 6 2, .triangle 24 1, .gapUpper 5 1, .triangle 12 1]

-- Original cycle 677dc6ed35d9f3970084bf088996b9028999ca5123214dc702e7053d21e27c2c; original global index 8041.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 67ed54ff00d3b8f02c20b76583557ad6dd7aa7eb9c9e0e14993de39a46696962; original global index 8079.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 6839fcf9c42432e273bb1af60c6eb6982117224366eca0c4f4539e9e69479411; original global index 8104.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 69407bf57f26021a46d08a35c25ab01c4a4fcaaf40d3da0cc9838dd347ce625b; original global index 8187.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 69e4eaa7a2ddc4f851ea8b0bcab642c6a791c3bbaf1c9d89721ff73f770bde18; original global index 8243.
def localCycle00130 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 6a8873fceaab59bfcc5078c56db1544cced28c2cc67443f2d297b988267b5eda; original global index 8296.
def localCycle00131 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 6d160d2e9c82f2eddbea0879d39aa982555c541769cad5c2a0cfa90fd3538764; original global index 8483.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 0, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 6d6787cac9c4150177382b34af17549f2ea26ce38819fd594e45ac4c6637a79f; original global index 8506.
def localCycle00133 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 6e14df10ab926c65627f05af097e4a377118b43b9c3fb4833b77a44019924694; original global index 8548.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 6f49f7a84deba72d6b3ba2244c191d4a1c061fb7b252cfd5268781885eb6fb99; original global index 8624.
def localCycle00135 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6fc68053364b79e669116661f05d3079b95cbbb85a8623a0ec89d319c4c4d106; original global index 8673.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 704b6cb1e1f33dd77077d3262281d27d77aaec123524e52662eb5d0b538f7aca; original global index 8700.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 72161fb8de2412b0a7f927c98f6de00c6375a899b81311cdbacb7337bb6b7a35; original global index 8843.
def localCycle00138 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7263ac8d2b5a6c8b5e1d3b246f79328caed5e0857b6e169468d62105c099cfae; original global index 8866.
def localCycle00139 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .gapLower 6 2, .triangle 8 1]

-- Original cycle 72d1494962c7ed7f13e4e731c7cf60296359c9f1acba32f1bf913659d53f8885; original global index 8895.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 72f59c25aeb8ed93b0d30964bba574721cdb748b370b4630717c1874d34aae86; original global index 8907.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 7402175d5e96fb56493ee01c0faa9a9e51ec130390efb8e60eff18f9afcc773d; original global index 8998.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7407f547a131912b3351e7094b3c72641d9be3de43611d18c0f4f8d16ee160f2; original global index 9002.
def localCycle00143 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 3 6, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 27 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle 758f89e06cfe7d9876e16183dc2cc34862865b3517924a89517cb2c3641fd880; original global index 9110.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 76cc0f99481a2d81d5a9dfe6173077484f45bc475a150d38df0634cfb0c298d2; original global index 9194.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 770fa4102e711d9f48d5fbdbed00b91b48be810fd979d92c5dd27569ca7c3c1f; original global index 9218.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 77dede5f8dda4a38335830410793d251f55fedf97e5d4661ec16c780593d3021; original global index 9270.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 78c074af78725c6eee57bd8aabbf10212d61cfddcce7b8088ab9b1c056ca557b; original global index 9343.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 79bf1f6272e413a4c8c83b1043c845c6809eafbbe7982b5a66c347b332f12e6d; original global index 9418.
def localCycle00149 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7b95a95bf871ddad942e5d781c76f02426de4b38ec7d3bc58ed01f5d1022250a; original global index 9564.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -3, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle 7c8a60a7bad7c2f610c070032b4b6bf9ea201448e2a6ae0a1727ceb30fa90ef3; original global index 9637.
def localCycle00151 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, 0, -3, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .gapLower 3 0]

-- Original cycle 7c9610252cac09949d3da98ea4f0ec346f88583117ea4c105e242101e3fa8e43; original global index 9641.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle 7d4ef7513d157e7c6e21beff726200790f69ad9e705ae3eb4b483dabe5acf4f9; original global index 9712.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle 7d5f9b57e64d728a49530a8363855abd638e30701a181d1d6f9c007647600185; original global index 9718.
def localCycle00154 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle 7d7860e877a3d6df0c2a2c73e562c61b2db0ba4f2b7e75ac292a009dfc79a942; original global index 9729.
def localCycle00155 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 8 2, .triangle 11 1]

-- Original cycle 7dfbba5e73f0f9083cbc0b2f595c57530c2052231335e16259203e838e83a2ac; original global index 9784.
def localCycle00156 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 7fcec82d9400dc914e86375b7bb317f9fa675220c0ce3cfac45d98c962f5ac83; original global index 9913.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7fcf2002445302d7278f7a898393b60ef8b761171878a2e5bd659deb93843435; original global index 9914.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7fd1e7cb73e9404cf72a2087dae256679a7b55f0897469e2ac6e8c7266ec383e; original global index 9915.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .corridorLower 4 6]

-- Original cycle 7fde1129477a8fab458db179d43ed98d0d51d538944acf4a50d63d154dea24af; original global index 9919.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 81550e999dda738b5c51e001d02570be8e3b393f8a9b7ec7814c53bdc0b4912a; original global index 10045.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 818aed20cabaa910c0e3be014fb6c26b3f474aa787d2dace2983c2cc19f0357d; original global index 10061.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 8277f173c2187c87925a5b75a512824054a5e07adcdfd0005ba7142aca2800f4; original global index 10124.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 13 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 84a0f824ce765f295a602d3a1b78ce6af3b502ab8d208fb78ed5a5d48dac629a; original global index 10300.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 870019dd9eb5a31197a0b43b221b3d94922eda604cf53e19f0b5bf2373b43d72; original global index 10471.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 870dab8850d3b1db6256fff20c472dfe7fe3b2343b0a05e11803070af324aba8; original global index 10477.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8807ac502149d5b2840c9d219ae7f3cdd74382aadcfc4e48b6c8a812d7cfa668; original global index 10549.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 886f83d96a9c82ed34919c6a943835106f169d5c5c97c6b0891873492af54621; original global index 10571.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 89055d5f56a6113fe966dcf56ac18b62c3eb112d04ae4c0bf116052de08e1fd6; original global index 10607.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 89738be5660fb3d1d6a14bf636e3c2d47ba53054b6bbef2fbb90fda119a24d2b; original global index 10639.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 89df97c038abebef38738ec32a5c09908784fabc4216c93d81d9e9f44e25cef9; original global index 10682.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8a120039499734d1b9f9c3daf2ac98ca6abb1afc5ce73a7321597a64a10c6db6; original global index 10699.
def localCycle00172 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8c76616b121d6407ee5f63f44047809baa296d55ef3d39f63d6cad506d4e51a8; original global index 10868.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle 8dcc10854dd98d1215a9e662ff3b9ffc69ec89a246deb868ae1536b0dcb79a75; original global index 10973.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 8f686239381e99cb6a727d5d4b7e90539fb188214b2ebf9c03793930e1cd92f6; original global index 11097.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 90db02fff53da3a1a27de01ed023112a294d8f4eba00cd11a721128d944e95e5; original global index 11216.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 90e722e8ff746b453d69e631f88d2146a2fcc6a0e16d6545f83d6fdbb52fbd09; original global index 11220.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 916075d0ba96281aa5f510cdbc083b0f5b082a6ae95feadfa72db13eec7aee2b; original global index 11261.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 9293dd3b53a59cfc038b1e73800fec37158132145a04f1aef29d8c895018a862; original global index 11356.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 92c9323b8216ee52cf07454cb989ca2a324c03ec11e88e927f8ae47b23738c62; original global index 11375.
def localCycle00180 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 92d27e7bc556430719236317d6bdd9bfa3d69df5c23cd596041445e571c54082; original global index 11379.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9456b7f4dc9471516e126e37e780b02ace573b823d8b81d1366074e6854400e0; original global index 11511.
def localCycle00182 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 957e593bb7abdb984d4f35c7f0cbf418f2ebfadafbdadb9fd09ee056f1635968; original global index 11619.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 96c7131d1456237406832fa266618f8268ba5d3b7b666d8a7509bb990fecef06; original global index 11725.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 97698ae8076d0d549afe8353f7f2879e97e13aa58d3312fa119186ce8c9193d8; original global index 11766.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![4, -1, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .triangle 11 1, .triangle 21 0, .gapLower 3 0]

-- Original cycle 97d1d93301846f3b8f308ca5334c366a3a3331d1707334c22626750634c60b50; original global index 11791.
def localCycle00186 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 98b58a8d7bbce0bfcaec8f8cf05f6ab20e00da73a60d95bee9bac2dfa8d1d8d2; original global index 11861.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 999e5bf580ee10259672891b7e977cb37ce36450e0cc529654cff7d6215c7c3c; original global index 11928.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 5, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .gapLower 5 3, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 99c4aaff9e346bf61d57334658b525039664b163e5a1503825a29fd0db3a45af; original global index 11938.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 9aa2754d6f1003365e7bf84c9a7a1142e82dd0f3d7cf753e028c222dcb89dcc8; original global index 12015.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9b22f29d04e3f10a480256e136d53c8f138f7a31439a5a7a3874340262795fa3; original global index 12061.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9b675d9183e2f934722bade7b6dea5e615b67f45a5c0c718a40f982f5ebadd6a; original global index 12085.
def localCycle00192 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9bef5eaf3a6461265f579f3cd319a056604b5396066a27a08b752b5a3efdaace; original global index 12127.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9dccc4f771008661f5b9d5f75a159e4ddfeee4c770ce31ba2ff99072db412e06; original global index 12277.
def localCycle00194 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle 9e13c2077d45087df5f211376e126fcc0895a3bf0c728f156959e42bbffffc59; original global index 12300.
def localCycle00195 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9e5a0566a4233cec4b208f0d8f646a4b71f8d579d69eb10f18c7a4b7a9bfc0b9; original global index 12328.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 9ebd2f642ff3a7a38eb9c732988f9cd0bb1b0e389a50c8009e2abeaf33bec107; original global index 12358.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9ee4adaa911f515564c1168a0708be699840d39138d2eaa7c88316086166c407; original global index 12371.
def localCycle00198 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 23 1]

-- Original cycle a140b1d76f7ee24d4b6d22836b81c5011cddba96d05aabda0b564a302c0cf928; original global index 12538.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a14cd180501dc6436813ae5976e508dae32398fbcb0fe7d606d3b5f0da5437eb; original global index 12542.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a2905425fe55e04d8c4471c362526e20dc11f32a44018ff73c09dc9311f49fe7; original global index 12646.
def localCycle00201 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a2feead3a15b8a1ab471fe7c1a1c017e35bc9401c08d15aad13908c0efcbcc7a; original global index 12675.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 8 2, .triangle 11 1, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a40402dde71e85af6ba87c65c5e6f03120f064eca7e43d0058aeb1afd7383465; original global index 12752.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle a446f1a5e2c81eb285ea38bbe41f7ffebd80d11b56f1c22ceb6b12b2f604c79b; original global index 12767.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle a4fa15093a13e46afaf8b26e1282acab8f87d7d588ee0c392b0e84b564adfcee; original global index 12820.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 1 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle a5183f1526e40de9d230683e903a642a53da8e48e3b0cc70aab0255832ae9cc7; original global index 12832.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle a7173c611f3c950ca583aed29bd006d03d254dafa4d5334cfa686fdc7a940fe9; original global index 12989.
def localCycle00207 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Original cycle a810fc87089a82a6ea53fa41b5f19021a85323cdfe4639be635454ad6cff89a0; original global index 13087.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle a9c3933ce1e1b4ae7703dc6bfba95dc75baf81470090993131a483c445287335; original global index 13218.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle aa0a1c4f350f1828c423c5b632f15fe569eccef58d5b8469392b34d09dddf72c; original global index 13236.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle aa1ad13e14e8afb49b1e7068b705ddfdabd2996516b13acb85ae18c549dd0d42; original global index 13244.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 0, .gapLower 1 3, .gapLower 4 0]

-- Original cycle aa36aa17a9f732f854e2002e05fc0927a8b4bf5dc330c2b39de03f9d4368ae22; original global index 13251.
def localCycle00212 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle ac065dd8f9344ef6a3b3990e48f2059c2b382d155dc035e061dc9700265d7cd8; original global index 13408.
def localCycle00213 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 0, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ad5cdd9c0f90bb8bc5277ff81392dd87b90d524138fe5c0ffc555d58f593ebd7; original global index 13520.
def localCycle00214 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .triangle 21 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00215 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle aed0b83bc875f01e5d2a5691f0a5d1e896f125a15476453e23f3a19366f6af1e; original global index 13645.
def localCycle00216 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle afbfb00861ad5da8fead6d6a2a3d27d717204c6022b31d0a75bcb824f9ff6e4b; original global index 13729.
def localCycle00217 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b01608703774a8e3a1be283b89a07d4931d76200560445d8a7ca2c1c644ce67d; original global index 13746.
def localCycle00218 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle b0720ae9241391e2c60b76cdaaaa96d90d82105b351fe3da0c7db638569f50ef; original global index 13776.
def localCycle00219 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .gapLower 5 3, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b170e5670a57e00e015bfe4b70eb00e7ec2e5d31ebdec12e2e3bcc14b11e3fce; original global index 13866.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 0, .triangle 6 2, .triangle 9 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b179f5057aabf83c5b44df1cf7eeec89571d94cf2b04dcb73218db92603733f8; original global index 13872.
def localCycle00221 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b2303bacc672a8f7c199df375166841753f00fb80e443472174ef31b0958e5c6; original global index 13923.
def localCycle00222 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle b3668cdb16c373f311e4b386ebb6980c88bc89ebd533cfb07818810a4d4f17c6; original global index 14019.
def localCycle00223 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle b3dad312ee2b33ee6bc938fe207518aef3ed678b6900c1dbfe0da162d6b714cf; original global index 14045.
def localCycle00224 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 1 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle b42fa1c0d91cb3ee585522d2704492295c39ce92f40845331eca4b6d7343a501; original global index 14075.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 2 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -2, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle b564e81acb91cc0d438ec8773eddf21d975961ca6699697cb802bffe1d52173a; original global index 14171.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b769fd67ddbc67d426c652ee354fdd76757c55548cd9e6241eeb3d252b0e2111; original global index 14313.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, -2, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle b90f5edb37ee387e62a13c831817d6f87c052b05e0cfcc8dbdd8d497567d180d; original global index 14440.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle b9192e413cc5a6436e93474ba38c18166e0531b61920ba9f29a97d37895c98ce; original global index 14444.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle b9afaa2e60b10656899c8f64b58d06878d4d418a5689793f8be235704284fbcf; original global index 14492.
def localCycle00230 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 11 0, .gapLower 6 2, .triangle 24 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle ba0110980b5596ba186d7199d55f8663d98da12c56898ff7d9dc1084f605b024; original global index 14524.
def localCycle00231 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bc4a90008d6c9956544bd1a171d13f453baa41f5a68e6e1b99dbcc148e63e4f7; original global index 14697.
def localCycle00232 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle bc71a75296d5e4433cdbc4be7b7c2062173a9c0e9e32c2d85bd9cdd8e676b127; original global index 14705.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle bcbde7a574925e89832b9b82d7ca110fcc00beb3779d399d491775cece2bc339; original global index 14723.
def localCycle00234 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle bdc01f8fcc22eba7627a76ef357868f4c1180a9c72044df3358980de9746f675; original global index 14800.
def localCycle00235 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle c09ad27ce79c969813c9019e2bb975cedbda1427afe4c2f5e9b844823935ebf1; original global index 15039.
def localCycle00236 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c0b69f3ebe3c3fd5fc62dcb63b2bfb636f43e0ddca2317cabfa293a631d62605; original global index 15048.
def localCycle00237 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c1286a123307a1e98dccc97a2ee9bf8cfcb09a1b32c1252e8bc6a2797c03f68b; original global index 15078.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle c1ea8f393f0d4d3ca7435a271d0303964fae25cbb85c34a6590862f6a2232ce7; original global index 15140.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 11 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle c21ecbea28cf959cb4287d76e5c2fe335f6243f0be531f6cb5a459ceae8fd889; original global index 15154.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c226c7f85ab37c3d5ab45a0a8a77ea47537e6f74b5725333e1466ee24870d2af; original global index 15159.
def localCycle00241 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c2cf15a4078491e33c81d7a067f8754bc6e8c2e0fa9eabf6a4208c09fe5334f1; original global index 15201.
def localCycle00242 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .triangle 5 2, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle c3bf7ab53b020d6944eeddb29070e89093e27f5ecde505a293b9e069f4ddfb9e; original global index 15273.
def localCycle00243 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .gapLower 4 0]

-- Original cycle c493dade3da3d2a4b41494dd02e9edca3b21d6fca316117d71f0173b4d3860e4; original global index 15329.
def localCycle00244 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -2, 0, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .gapLower 6 4, .triangle 13 1, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle c4cf048695a7adcec94123a321a3b25992513ced995a025e534cc3da5257a32e; original global index 15351.
def localCycle00245 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .gapLower 4 0]

-- Original cycle c4d7256aea51878a1d18bcd5d1ff8c3e1661299e59ef1c2eb3f7bea37d6da38a; original global index 15353.
def localCycle00246 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .gapLower 6 3, .triangle 4 2, .triangle 11 1]

-- Original cycle c5101da9b20e0f261afbfeb22af1eca859b3b1ad88075e956ced4ac29a9822c3; original global index 15376.
def localCycle00247 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 2 3, .gapUpper 4 4, .gapLower 6 5, .triangle 27 0]

-- Original cycle c53b02f58c82bd64968e0386652a50c5aece4cccf672084930ae43cf6d16f51b; original global index 15388.
def localCycle00248 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c672977ab101aaf396c4d288fea8b42b7c4a61ff259a5dbaf5da64e913083acc; original global index 15479.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle c699c8d7f158a8d960d017f463a0ea7363e7313af05dabec8cca71b2e99fe9fc; original global index 15491.
def localCycle00250 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![4, 0, -2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .triangle 0 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle c6b1d41adf2ac66c1f2d602821026053bc785e322d3d5f678ff74a8c63b5df4c; original global index 15500.
def localCycle00251 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle c781294450e83b072d240a77a9d433680bcf3a881cee33ca1416404627715815; original global index 15570.
def localCycle00252 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle c797e5a0fb02de15c835b7b33db7d60202cb32434ce97cb36abecfa28edcb6c7; original global index 15576.
def localCycle00253 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c9ae2fca1e99071a83bf099277049c20c644a011901ddfb7a4220fb907699afc; original global index 15767.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 3 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ca0562c4b463077a64c044c265c871f62f59b11f4a8699bfec89dcabf757e9ab; original global index 15791.
def localCycle00255 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 21 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle cb5e6872d88aad9b4545c4a4d6b165e6eda8271b33ece8f4e7ba60fefe1b9a9e; original global index 15887.
def localCycle00256 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle cbc661c5d7b71dc234c7471b5c37ec11acc650c653edab86d86bb9cdd699a57a; original global index 15923.
def localCycle00257 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ccebb212458e5228ab160f7dca56d7541e1e7c4cac467d3eba5039eab3341c54; original global index 16015.
def localCycle00258 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, -2, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .gapLower 3 0]

-- Original cycle cd620650d5dbe385154cc00b647e0879adaacc678529489581b1153220626daf; original global index 16053.
def localCycle00259 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle cee467fb13270fd9cec5f6ba80c5f762f16a97cb692e16099af2a661bf67f7b2; original global index 16148.
def localCycle00260 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 9 2, .gapUpper 4 4, .gapLower 6 5, .triangle 11 0]

-- Original cycle cf4ea1dd32642e77337b1fa425d6cbaa6c9857270430e472e0fe45afd4839728; original global index 16179.
def localCycle00261 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .triangle 23 2, .gapUpper 1 4]

-- Original cycle cff912e2debd824c0f07328bf19c3831cb50d26ed326374489264f2c9b96ac0f; original global index 16235.
def localCycle00262 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d2516a414be3229f5ea27166634987a0456e2f567e7ecd8a80e0cd86c85f10fb; original global index 16408.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 29 1, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle d32cae771064c5cd1d0fb8621fd98956496f4013c39a812353f2d93263e4d99d; original global index 16473.
def localCycle00264 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d3678c49a993487dcb670e8bf518126da40714c5a0f39560653dbdb33084f0e4; original global index 16490.
def localCycle00265 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 13 1]

-- Original cycle d5e793060685d718bd7b203f484a7de3df165695c4632b452da2aa9491f0b8a5; original global index 16694.
def localCycle00266 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d641f8634ae2d90fd765c5868bde04423d7615397202a9dacbd3c7e06aef81ec; original global index 16726.
def localCycle00267 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d68575bc2ec84e8840c6d2fcdebb59b14ebd3b7db9dc70abb2215e6dae43c4ba; original global index 16746.
def localCycle00268 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1]

-- Original cycle d6b1d596f422e0c6c1d84f079512de4dea14fd13cfcae43d56c71ec76f390f98; original global index 16756.
def localCycle00269 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d72711b765374eac3aa4259b9834d4bbb8dd1cda390031aff60bc0299c563dbf; original global index 16792.
def localCycle00270 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d7c554ab5437b3c2af910b8b0e3b5e57897f2d7895ed3444bfcce0c0a7f29272; original global index 16836.
def localCycle00271 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle d8e48cbc6ebf54da8e5d954c0f8ac602468d5afaee419b5bd5dc498db4833fc6; original global index 16933.
def localCycle00272 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![4, 0, -2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 4 1, .triangle 0 0, .triangle 16 0, .triangle 25 1, .gapLower 3 0]

-- Original cycle db0b22525a8e3fbb18500db5e3c69de555683f85e80ee566138a6b0d564ad6ea; original global index 17117.
def localCycle00273 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dbc12c2289f800a16b121d9f0020929965be44f0377cf98cb28a3d4eac57f947; original global index 17174.
def localCycle00274 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dc0d0572f233d5fc7023a5ee29d9faf8615e8efebdc294cc730457963c67474a; original global index 17199.
def localCycle00275 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 13 1]

-- Original cycle dc3629dc42c9892a1d866749d05ac408d09d0eb000483aabca417cd7bad36dd6; original global index 17210.
def localCycle00276 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3]

-- Original cycle dd847097386f0228b04b000f27fcb2dc8f97c4cebc9b12369dfa913f3eb6ff5b; original global index 17318.
def localCycle00277 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dda7cc972e249f19e284b3d6249e6d2f48a454e3e5e69b0261b65a23eeec47ff; original global index 17325.
def localCycle00278 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ddf923e16ff91c7f2c1d5e4de0b7338ddf6f9bb3b29fb5eef522fbd5b4292084; original global index 17353.
def localCycle00279 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle df698c06e38321c2edbe85bc6331b37c241ea373728a209c384d8b5c60ced16a; original global index 17456.
def localCycle00280 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0]

-- Original cycle df75b09ae844f955a02adb2f374b837b62c586d3f9ec4eb48c6c0282fc1ceddd; original global index 17463.
def localCycle00281 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dfd34de2315a1e029ccf66c57ac0954d1a8d6092c73d20b9df8c9f9f869d0dca; original global index 17488.
def localCycle00282 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, -2, 2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e00f64b24dfedf7007fbc79fb7bfea73788ee7d6b8f210aeef2fc7a69ab02d8a; original global index 17516.
def localCycle00283 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle e0a064eb3816c1a6b1612a7c29e7b8182f0983f5c1ea006029d1fa674604b2de; original global index 17565.
def localCycle00284 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1]

-- Original cycle e10a65f5ef38324593da1596943927865865326840183e61184e4da6d5c57624; original global index 17595.
def localCycle00285 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e12a73b111222c022c5ec7fa04477c88fa8a71deb6637cfc318dbe8a1779bf59; original global index 17608.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e12de6ca108f24754e4d684cd16a7d52461f767f0dad14d677865510975f3601; original global index 17610.
def localCycle00287 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 1 4, .gapLower 6 2, .triangle 4 1]

-- Original cycle e28265b97e617a826e0f3d4450743b7c6bc77a345590e052478dc06a6e18c823; original global index 17712.
def localCycle00288 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 18 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle e29db16197af46f6d31d904b9d02bc091bbf5cf2dd27a2af0429f09262591057; original global index 17722.
def localCycle00289 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e2a688748a74af0cb9bf2e69e53b0c025e69a72349aa1dde4a1bcf9649bccf7a; original global index 17724.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle e53692488fd6e0efd1eaa2f5a72df66012ab62c890944621c2dfbc82caa10440; original global index 17917.
def localCycle00291 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 23 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle e5890e9bfc81e39aea80c78d1a15f5c20f967b75ba7ba6d4da7e05a5f69a4b51; original global index 17955.
def localCycle00292 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e61345ac4fbf7d5390ad9be5ba74f0975bff4310f684588be008a313c1d50a95; original global index 18005.
def localCycle00293 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e616594eca2d3a582fbb122251986cdd2de31bf3c521d2c859a03d1f09c08177; original global index 18007.
def localCycle00294 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle e6d3753f8ca03c66924d3701aca14227c5b7199dd5715341eb97afda34083180; original global index 18060.
def localCycle00295 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e71a0bcd26d2a148b05afd83656104704c56f25bc07d4aa38d0f8aabe6d75e67; original global index 18076.
def localCycle00296 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle e78828c6ae75c027ed530043b064f6b7baacea504d6a957bbeea5054a6555ace; original global index 18107.
def localCycle00297 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle e7b5f54cf315011a973e9fa1a36b3cc002d4f5bed14ee26abdb63463daeae32d; original global index 18121.
def localCycle00298 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 4 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle e7ebec6e9c76d00cc5ab8a8e12f59ed6fe993d9311a8e44247f915b85656c1e3; original global index 18136.
def localCycle00299 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle e8b1f903526d00b22782c504ce9455a4e0fc025c23550d7a0315ae3a2513a3db; original global index 18187.
def localCycle00300 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e97e9e54b81cae1cfc581b44e5ed116ba60cd0a79b9a11ca773fa5cc79c6be19; original global index 18247.
def localCycle00301 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle eaa35a0ca640e8e7f5b8566f5ee3a5d722f52c4d80823ef03512c336c0375152; original global index 18325.
def localCycle00302 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ebc60f4634d94da16807128b55a8917de683e6329b75f16319faa54daee3568a; original global index 18396.
def localCycle00303 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .gapLower 6 3, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ed77e966dfb64c8194aa2b5d10bb19fb2d47d94ee73c836dab79345d2fc7d5d7; original global index 18536.
def localCycle00304 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle edfcba1aac925e741598115bb6c40e3b532725bcd9993b9d28c60c8d34dde673; original global index 18580.
def localCycle00305 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ee22b45e5732af14660abe133ddec3116e899aa4aa8c8ef4984f6b95e7fd4641; original global index 18587.
def localCycle00306 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ee2ad24b9069e126f383c2e1dfc03694c80880ef82920d8330ff4d75775441ec; original global index 18589.
def localCycle00307 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .triangle 8 2, .triangle 13 1, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ee87403a7693650f9aa5119a8ceba2bd0b75905d3c7c6abc18661dfb610e8fc0; original global index 18613.
def localCycle00308 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 27 1, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle ef09441bfe18d3962bb667a8644cb91411bb579d257966cb915469263d351a02; original global index 18652.
def localCycle00309 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle efca9242784cc74d108434af22f820ecdf46a879d766dfd0a62f6aac873f6e77; original global index 18709.
def localCycle00310 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle f2f9977a969cba0ae9dba5ff3819e850dc8340c31ea18f9f7a294ed3b08c48f6; original global index 18940.
def localCycle00311 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f38bc08f612419d14f7af9e833f1ae469220a828cb4dc58fc9223f78fe38c37b; original global index 19005.
def localCycle00312 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle f3962acf16a35cb3c8e8fcbfc9c74dbfbf50d78b77595889fe3f27fe47094511; original global index 19006.
def localCycle00313 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 3, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f3c496c198d6e5fed52a3aaf179281933489c8ac0e7a44275352806d74133413; original global index 19015.
def localCycle00314 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 1 2, .triangle 11 0, .gapLower 6 2, .gapUpper 1 4]

-- Original cycle f429ddb87c4432edbb1590b00a7a6edc7b4e2f1b966dca0f6ea116fc14bef18f; original global index 19040.
def localCycle00315 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle f4880f4deae83201defbf2e9f6a6e9d5920d039d588a9e8f52c4fe313e3c808a; original global index 19067.
def localCycle00316 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle f5568c6207e794b73f041d75c4b49a8e6bb53e9eba8ef615059aab03346b4420; original global index 19123.
def localCycle00317 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 0 1, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .gapLower 6 3, .gapLower 6 2, .triangle 4 1, .triangle 2 0, .triangle 19 1, .gapLower 3 0]

-- Original cycle f5f18edd65563fad6241c0c099afec30a136d16a98f25bbd52e27fec21f8684e; original global index 19192.
def localCycle00318 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 23 2, .triangle 4 0, .triangle 0 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f693830174561d8b192f5e09f0c3bb7bd399541ab308f29768613d9881bcc740; original global index 19239.
def localCycle00319 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f6db57e3281c10222806f449b76493564c6df03ac1aa77e5bc623d0843b06d05; original global index 19255.
def localCycle00320 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 6, .distance 1 6, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 4 2, .gapLower 6 2, .triangle 21 1, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f7453c13e48f27cf95fdd6922c56293ca52741676d6089e4eca9164e41468fca; original global index 19290.
def localCycle00321 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f815f065e58ca68f85e783503b8d2ae91ea420175b99cf7a861396e679d8f3fb; original global index 19343.
def localCycle00322 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 5, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .gapLower 5 3, .gapUpper 1 6, .thetaLower 1]

-- Original cycle f9ce3700364b5cf5178a106966c67504da0cab20281bd0d456cae7a4ab974beb; original global index 19480.
def localCycle00323 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle fa4633fa4c8af24869fbc94eafcc4e13369352f6571122ebc7bd7add8bd71e51; original global index 19519.
def localCycle00324 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .gapLower 5 3, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle fa9b26bf657654097742311817d4cfb90edf5f30b341178d7ad73f3bfa9caf83; original global index 19551.
def localCycle00325 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle fae0ed7214d5b6d60c36cba16c611ec710d8a72402d482efdc51ad7442ef985a; original global index 19577.
def localCycle00326 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 2 2, .gapUpper 4 2, .gapLower 6 3, .triangle 4 0]

-- Original cycle fb65f6b4baa87b8e92b32518e194bd45c4c7e2bb87c3ca267b137e07e546d5ff; original global index 19621.
def localCycle00327 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle fbd17858422e3657e33cac94bef95dea819d65bdfc30a77d3b2d1e7d14f607c2; original global index 19659.
def localCycle00328 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 13 1, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle fbe64f28c3bee9b64773c4c96fdfafc66640644af15c69af22a498b5d4485735; original global index 19664.
def localCycle00329 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Original cycle fc3319a69410b774e18119566f5069f580180d6c914675ec4692febe0735a360; original global index 19695.
def localCycle00330 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![4, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle fcb8a4934c54ec234eab161af5f7c3657e8167c03285a7bc57b2847d7d3ac6c7; original global index 19748.
def localCycle00331 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fe3a3d0089b05ec6c305ad5949265489f96e2b828d4e5d5d8ac07fe6e4321fa7; original global index 19871.
def localCycle00332 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapLower 6 5, .gapLower 6 4, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle fe677e78688be3ecaeeb147b6b258c66791f20024fc0460ab5dab1d19676de2f; original global index 19888.
def localCycle00333 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle ff307bcf6d0618087621a7dd17241339ca02f24812ccbb0460e0c7930231d5c5; original global index 19951.
def localCycle00334 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 23 2, .gapLower 6 1, .corridorLower 5 6]

def library : Library := fun id => if id < 167 then (if id < 83 then (if id < 41 then (if id < 20 then (if id < 10 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 7 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))))) else (if id < 15 then (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)))) else (if id < 17 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))))) else (if id < 30 then (if id < 25 then (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))))) else (if id < 35 then (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))))) else (if id < 62 then (if id < 51 then (if id < 46 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))) else (if id < 56 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)))))) else (if id < 72 then (if id < 67 then (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))))) else (if id < 77 then (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))))))) else (if id < 125 then (if id < 104 then (if id < 93 then (if id < 88 then (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))))) else (if id < 98 then (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)))))) else (if id < 114 then (if id < 109 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))))) else (if id < 119 then (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))) else (if id < 122 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))))))) else (if id < 146 then (if id < 135 then (if id < 130 then (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))) else (if id < 140 then (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)))) else (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)))))) else (if id < 156 then (if id < 151 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))))) else (if id < 161 then (if id < 158 then (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))))))))) else (if id < 251 then (if id < 209 then (if id < 188 then (if id < 177 then (if id < 172 then (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))) else (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))) else (if id < 182 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)))) else (if id < 185 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)))))) else (if id < 198 then (if id < 193 then (if id < 190 then (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))))) else (if id < 203 then (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)))) else (if id < 206 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))))))) else (if id < 230 then (if id < 219 then (if id < 214 then (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)))) else (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))))) else (if id < 224 then (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none)))) else (if id < 227 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)))))) else (if id < 240 then (if id < 235 then (if id < 232 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)))) else (if id < 237 then (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none))))) else (if id < 245 then (if id < 242 then (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none)) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none)))) else (if id < 248 then (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none))) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)))))))) else (if id < 293 then (if id < 272 then (if id < 261 then (if id < 256 then (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)))) else (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none))))) else (if id < 266 then (if id < 263 then (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none)) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id = 265 then some localCycle00265 else none)))) else (if id < 269 then (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none))) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none)))))) else (if id < 282 then (if id < 277 then (if id < 274 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))) else (if id < 279 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none))))) else (if id < 287 then (if id < 284 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none)) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none)))) else (if id < 290 then (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id = 289 then some localCycle00289 else none))) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none))))))) else (if id < 314 then (if id < 303 then (if id < 298 then (if id < 295 then (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none)) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none)))) else (if id < 300 then (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none)) else (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none))))) else (if id < 308 then (if id < 305 then (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id = 304 then some localCycle00304 else none)) else (if id < 306 then (if id = 305 then some localCycle00305 else none) else (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id = 307 then some localCycle00307 else none)))) else (if id < 311 then (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id = 310 then some localCycle00310 else none))) else (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id = 313 then some localCycle00313 else none)))))) else (if id < 324 then (if id < 319 then (if id < 316 then (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none)))) else (if id < 321 then (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id = 323 then some localCycle00323 else none))))) else (if id < 329 then (if id < 326 then (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none)) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none)))) else (if id < 332 then (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none))) else (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id = 334 then some localCycle00334 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 50 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16384)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .low6 (![95, 286, 287, 32, 97, 12, 47, 176, 300, 326, 166, 81, 4, 262, 211, 35, 170, 187, 284, 245, 52, 243, 102, 9, 326, 159, 160, 5]) }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16385)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 0, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 274 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16386)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 274 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16387)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 207 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16388)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 294 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16389)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 182 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16390)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 184 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16391)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 283 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16392)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 50 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16393)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 257 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16394)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 131 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16395)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 41 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16396)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 133 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16397)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 3, 5, 4], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 3, 2]], proof := .tail 103 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16398)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 277 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16399)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 277 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16400)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 312 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16401)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .low6 (![95, 252, 287, 229, 49, 20, 109, 239, 276, 208, 113, 135, 173, 174, 137, 209, 278, 130, 317, 153, 288, 152, 225, 62, 208, 254, 29, 269]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16402)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 66 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16403)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 290 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16404)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 257 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16405)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 4, 3, 2]], proof := .tail 88 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16406)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 41 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16407)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 290 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16408)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 3, 4], ![1, 0, 6, 5, 2, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 188 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16409)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 24 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16410)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 55 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16411)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 3, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 0, 1, 4, 3, 2]], proof := .tail 322 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16412)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 248 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16413)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 4, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 324 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16414)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 165 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16415)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 290 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16416)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![4, 2, 3, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 189 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16417)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 85 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16418)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 232 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16419)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 156 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16420)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 223 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16421)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 50 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16422)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 123 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16423)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![95, 252, 287, 40, 221, 15, 256, 216, 21, 72, 253, 68, 89, 39, 72, 57, 306, 6, 139, 100, 111, 157, 285, 279, 72, 179, 199, 8]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16424)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 63 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16425)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 295 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16426)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 177 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16427)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![2, 3, 4, 0, 6, 5], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 61 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16428)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![2, 4, 3, 0, 6, 5], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![95, 252, 287, 40, 155, 13, 200, 216, 21, 72, 124, 260, 282, 39, 72, 124, 260, 235, 139, 26, 275, 158, 246, 268, 72, 265, 124, 260]) }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16429)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![4, 2, 3, 0, 6, 5], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 87 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16430)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![95, 252, 287, 17, 150, 15, 197, 216, 21, 331, 146, 38, 36, 39, 271, 57, 306, 144, 7, 218, 111, 192, 227, 110, 293, 270, 186, 281]) }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16431)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 299 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16432)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 48 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16433)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 315 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16434)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 280 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16435)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![3, 2, 4, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 219 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16436)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 319 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16437)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 75 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16438)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 241 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16439)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![3, 2, 4, 0, 6, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 136 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16440)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![2, 1, 0, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![95, 252, 287, 40, 151, 15, 190, 216, 21, 72, 181, 2, 318, 39, 72, 57, 306, 201, 139, 272, 44, 164, 258, 250, 72, 105, 231, 112]) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16441)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 33 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16442)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![3, 4, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 90 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16443)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![3, 4, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 4, 0, 6, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![95, 252, 287, 40, 155, 13, 305, 216, 21, 72, 124, 260, 14, 39, 72, 124, 260, 126, 139, 26, 275, 242, 246, 268, 72, 265, 124, 132]) }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16444)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![4, 3, 2, 0, 6, 5], ![3, 4, 1, 0, 6, 5], ![2, 4, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 195 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16445)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 3, 2, 1, 6, 5], ![4, 3, 2, 0, 6, 5], ![4, 3, 1, 0, 6, 5], ![4, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 333 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16446)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![203, 161, 154, 93, 127, 15, 98, 193, 238, 217, 217, 217, 217, 78, 106, 106, 106, 106, 215, 74, 264, 64, 116, 304, 64, 34, 11, 119]) }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16447)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 46 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16448)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 2, 3]], proof := .low6 (![203, 161, 163, 94, 114, 12, 1, 193, 148, 217, 310, 289, 217, 25, 213, 334, 80, 106, 69, 67, 296, 23, 121, 56, 0, 332, 86, 178]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16449)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 2, 3]], proof := .low6 (![226, 122, 198, 104, 45, 12, 129, 30, 168, 291, 266, 266, 266, 19, 22, 79, 307, 53, 298, 328, 267, 125, 118, 303, 261, 31, 244, 120]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16450)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 2, 3]], proof := .tail 204 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16451)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 0, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 134 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16452)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 302 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16453)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 228 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16454)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 108 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16455)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 108 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16456)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 309 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16457)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![203, 161, 154, 93, 73, 247, 71, 193, 238, 217, 217, 194, 217, 78, 106, 106, 194, 106, 215, 74, 194, 212, 116, 194, 51, 18, 308, 194]) }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16458)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .low6 (![203, 161, 96, 76, 143, 20, 109, 193, 82, 217, 65, 217, 217, 25, 43, 140, 106, 106, 141, 99, 84, 222, 210, 162, 162, 254, 169, 180]) }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16459)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 257 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16460)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 60 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16461)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 149 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16462)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 204 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16463)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 91 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16464)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 91 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16465)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 171 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16466)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![203, 161, 154, 321, 73, 247, 191, 193, 238, 217, 217, 194, 217, 78, 106, 106, 194, 106, 215, 74, 194, 325, 330, 194, 273, 18, 292, 194]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16467)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 92 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16468)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 167 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16469)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .low6 (![77, 251, 230, 107, 185, 20, 220, 145, 101, 255, 10, 10, 10, 314, 313, 42, 196, 196, 3, 27, 83, 83, 172, 233, 28, 128, 54, 202]) }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16470)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 236 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16471)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 37 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16472)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 147 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16473)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 58 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16474)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 323 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16475)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![203, 161, 154, 214, 73, 247, 109, 193, 238, 217, 217, 194, 217, 78, 106, 106, 194, 106, 215, 74, 194, 320, 116, 194, 70, 18, 117, 194]) }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16476)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 224 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16477)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 4, 3, 6, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 59 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16478)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 4, 6, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 297 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16479)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 4, 2]], proof := .tail 259 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16480)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 0, 2]], proof := .tail 316 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16481)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 329 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16482)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 4, 6, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 329 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16483)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 329 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16484)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 16 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16485)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 6, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 0, 6, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 205 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16486)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![1, 6, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 138 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16487)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 183 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16488)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 138 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16489)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 91 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16490)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 91 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16491)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 171 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16492)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 142 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16493)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![1, 6, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 311 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16494)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![1, 6, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 58 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16495)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 323 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16496)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 6, 0, 4, 3, 5], ![4, 1, 6, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 263 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16497)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 206 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16498)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 175 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16499)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 0, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 205 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16500)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 3, 4, 5], ![6, 1, 0, 2, 4, 5], ![6, 1, 0, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 249 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16501)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 171 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16502)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 4, 3, 5], ![6, 1, 4, 0, 2, 5], ![6, 1, 3, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 323 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16503)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 0, 4, 3, 5], ![4, 6, 1, 0, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 234 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16504)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 2, 4, 3, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 0, 4, 3, 5], ![6, 4, 1, 0, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 205 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16505)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 0, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .tail 274 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16506)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 2, 3, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .tail 115 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16507)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 2, 6, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 0, 6, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 0, 2, 4]], proof := .tail 301 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16508)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 6, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 2, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 240 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16509)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 6, 0, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 237 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16510)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 2, 3, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 4, 0, 3, 5], ![1, 4, 6, 0, 2, 5], ![1, 3, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 327 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16511)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (16384 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 16384 ≤ id.val) (hhigh : id.val < 16512) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 16384)) = true := by
  let j : Fin 128 := ⟨id.val - 16384, by omega⟩
  have hsum : 16384 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (16384 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard128
