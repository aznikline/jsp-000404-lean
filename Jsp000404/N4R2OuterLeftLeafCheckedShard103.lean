import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard103
open N4R2OuterLeftReplay

-- Cycle fingerprint 00305c5920f6f9e47f82d1dcfd1ed223eee9cf57d08c01a1bae4acf03022e879.
def localCycle00000 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 00b76fe2fcdc68f943945698ce66092ff38a32c430d8d2d1473753eda89f01e3.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 00f7e22969bb0e3dcbc710106e790a98f4713d6b56c27bb1c2f4d8e3e3eae646.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 041189407a8f0ee6ab549a713fcbe92fd7cd16645555aef3583d30c5e6c60b17.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 2, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 042e19ea155a6535fe24c97c270029f983b06cfdac85b14b6ec5529df7479ecc.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 05314da950c662f224cbac986c2993770effd8da682c146ae7f9e84b64a4a78d.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, -1, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint 054547e4b64ac7d681dc58aef6042a1765e24b0ad527423b71cea83e3a0e2b07.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 05ccb1bd1b7c7834bfc9a7b6f31698c4fa58b173b252ada9dbb1540bf045f72f.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 0614a8dc1699f77017a90e131f4a8433d6a9969743008b2e29aa7980ca68234a.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 06719814c59f8def6ddface8c3afe8cb0d8f6ab4c7a2e2ee78e2acd85bf15535.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 06fb0575831741b26accd09933c89088e2946c78d061400bc47698e632ddfc2f.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 0bb2d499af8d1b6ba1617c3f433d9054bd71556b9034e1e936191af03feaae61.
def localCycle00011 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 13535f99b105865a8ff3e765a76cb48427542d979ee7df6d6b8854981fba1515.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 14c91e7ff45ca027be1275f8133663f82fb22452034266585f89e375e6de313d.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 1583f3e83cb6a550a8129b4d1c0361734bfb96fb5ad65f77b6812bd06557d71e.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 16529661b1162296b4304e0e2895f54c1a534bde5cdee330b0a2fd43708d1edb.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Cycle fingerprint 166155ace295b8e5400b075568b4ce6bbd2062987963eb5c24bc5fa39cd59d62.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 2, .triangle 10 0, .triangle 5 1, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 186cf184ededf98692bc76191fff4dcc21e74d7dd44e0d70875586c4b10acc45.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 1d503706b62587102934d26c8d7a74d7131453e8eda2cc66d73545d49f9fe9fc.
def localCycle00018 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 0 2, .gapUpper 2 2, .gapLower 4 3]

-- Cycle fingerprint 1d88919bd5de99935e4d76daf5c44b4ec07d62c9812befb8b86228a18a49d3e0.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 1da52dc78e4aeb0f838e007f2219b2cfd8b16368598cdff17fb86a99383aacb6.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 2002859d2b28c39c59ba774e68d2d8d4479fc0bf389d697121f2d0d116c0f614.
def localCycle00021 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![0, 0, 0, -1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 27 2, .triangle 29 1, .triangle 16 2, .triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 25626851556371fec96d754985cdac336f3c0685663f485dc9f5637d11b90184.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 27824363e1d7101ea2ac169e14e668a3077d50595185bcc53d75334983627d12.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 2a4a97db3ebe95287b8cca7a5248fbebc40c47696f4b3116d1e57973d9a81305.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -3, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 2aa1f5304ac6c9ca4b14984e88f477e59e10b8cf880628d9660d891f9ae72942.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 2bf149e12a217cc4c740c8de9d186aba668f0bd457671487ab0f6e8cf901d838.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 2df24bdc3d97073b8e260299e26fcb9ce32683bdffba916be21f4bebe4ab75ad.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 3 1, .triangle 0 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 2e32a0f6c27015183eaf82c3b9e99140c2cfc0b63e8b5c68331d1c5ad687fdde.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 329003f79c053100348d69674c1da371af934bfe0fc74ce50fe11a0663591268.
def localCycle00029 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 361511cc34812f18d7444b9a4921b2fb4633a8b8a2d07fdac39d5b34ff51056b.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 39d342d630fe34c6623661b0fe6bef8a93eb405144b6c0ff3e6c1df46eb481a7.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -1, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 3cf06be6dbfa6b76fff24ad2f946548f441686aa05f0a9ef636d6619a5fb2f55.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 3dc3947d17de386671ea0d890dede0507cb4c7d9aa70fe5f9da74fe0d6c8cc99.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .triangle 2 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3deb092e5a59414fd1d0705419d36b5e94346332044c80d2f3b481afe24c24a6.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint 3f6b5d9a8e3379a0b5e68c18b376cb2ef0ed2a1263220b240b056bfc21ae0111.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 4003cea41c284219a2beba2890acb8cf3655850398a7d8bf3805c190a60b8482.
def localCycle00036 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 41e63433eba353220d6bb4ed43b27a917de0e89ebf5acf9b96593651e734d843.
def localCycle00037 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 434237c25f48d9da9e6a8fb28dafa9ed484fe27b3a2cef6765bd48f09517541e.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 4443e501bda642c45fc4cdb641376510dfd92d631db11f8f46d00b3fd4f9ed4d.
def localCycle00039 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 4ab0bbc5bdf06ef85c25fdf48b8f08bb4c87f0a92dd11d82dcd9d78a767503e4.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 5 1, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4bb6b0a6b73dd7a0ee613417c62e1d5282ec3e9da8109f284b13dd8ba510ca03.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 4be612f4215feb2f7c58fb1f436c0a6230012f3746024e6180468443671628f1.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5]
    constant := ![-2, 0, -2, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 4c57c2928c0f08255c00b6bcdc8d2f960f4dfbf59dcd2c7061e71902b5543d23.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 4ff9ea16835447d5d1f85c5b79dd2dedc3b30f607c503ab78bd3065e8dc99c6a.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 512ded67a5b880711f6b2f9b659045379f424d89da40f0433d8513dc8c38e7b9.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 54a90286159deea231cfe473490a94c94850059226218483880752f0b1892938.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 56f70a0340497caefe582f6879b691209e45adf5e951dfbe12d20f487875ef3c.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 58314b3e2433fcf93d64cec3227a57dbebbe99b0b957214894c9ce3a60fd0508.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint 5b5121f05b0b50ec7c1338ba455f2b598d8ed8ab8b0ee38c4eadbc32033d59a0.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 5f8456e23c8c0a4d7f7107e1ff4b30b5afa4822913c3ded2a3094ca20e4c68a4.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6156fd5c1db7500490a504a7ed0b36d95b1cae384008c170594149d653b918c0.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 654920524f1069249648a1385281060861f8d4043e5590bd264314c0486bbbfe.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 66d4d8cc0cfaeaf26e02416c4de885f5df9ea6e4b595a8341b9d41bcdc51ac8e.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 677bc84ccc3d941c19572df824996984d25a895332974ecad6773fccde4812f2.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 5 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 68e5aa4e4076cb21f92c69ec6f94ac9a02d50a3a3d3b6ace460a98f0c8746351.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, 0, 2, -2, 0, 3, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 1 0, .gapLower 0 1, .gapUpper 2 2, .gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0]

-- Cycle fingerprint 6a1643d7026f8f99f8264df3a63f85f8ce8d772c6b93759c7bd58f69ecf8792b.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 6b1213d9c74d0dfc072402ac38eca6654fe7e3dd9acec88b84c54cec78dd2c27.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6b9b93ad56db8fa669272badc8957430904ab464918fe7e6897f316cceecec5e.
def localCycle00058 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 2, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6bf2fa6a748b865fc11690860f2bca1026b829ece9ddb3589da42bf1e96d24d6.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 6ca116ebecbb3d46ae29ee2ee1e2b82827220418a3aef49c347072efa29852f9.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![1, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 24 0, .triangle 14 0, .gapLower 0 4, .triangle 1 1, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint 6f77ae346a07c2c2be1f950b5b601833359ee6ec43193501301d41ed8c0b57ed.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 70da3b552c5af04e765ccb5f41883edeb88089169b89ec021a244d942f34c742.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 71950e6ec3744598a746a6a7ab537b2790f3e1b7fa280334b861aff7c1d33c2f.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 759e7f0c846eb8157efaf4a3493913f7d4ea3bb2dca46b55ceba3993866a3963.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00065 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 79581dd5ce0f1e0bcf6af8f2408dc9cb124a48622c87e398b512a64e6aa1d588.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7a086725c9a3d6f410f35ee6080352c3118da2ea5f6efcaba175035b38af3514.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7a6d8d8a3286876e65367cb034d9c5410bc1747bed3d7450d1fdc9814c92d0cd.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7aedb801da1bbf8109a330994eb31f3316e42f49f8752578f36bda21e6734898.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Cycle fingerprint 7cb87c5368527a3c6d70c1c536b8143387a0c72a0becfe48cf563a6264429a1e.
def localCycle00070 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 24 2]

-- Cycle fingerprint 7f440546f98b309681a514aa5ac0ce8f8ea29b142ff1ca29e482e88c99ec5b04.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 8030a3d1ce5b2c0381590fa44b943ad53b6d720881a25756c7c12519cc44ddc8.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8337ec49fe4a2255d3b0c938286ab51cfd978bffcf51e0f5394a1f295c208242.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 84cad536f9bd5a9e1731785597a4c260edb8740df6e6bf215d7bf9b1ac715fd6.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 10 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0]

-- Cycle fingerprint 86f7ea3972e0e04d0183a83de66b4c63c358eceeca01017414e431ad396c3225.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 86f8ac5023822079258d412b43fbe0a6229ec6973d295b8b3ad3e409a907a03a.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 1]

-- Cycle fingerprint 8a7b17255ad492895cc5915876625014cf16cd8805a9812378a245769c203755.
def localCycle00077 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 8fcd8661fd70f6a108d5f79f183785418e5d28f878dae20b9645ce41dc249eec.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 9163adf616f851d8a22af0c1f19fa7398c4f9db13087b12e80515877f813db64.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 931cc3a2e0576de9e44c258f2c0a589da6fa52743de5717e3fedaf519851835d.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2]
    constant := ![2, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .gapUpper 4 4, .triangle 32 2, .triangle 21 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 0 2]

-- Cycle fingerprint 93fce1e9aaa66578333bdf97a3d35a5107cceefba31042ea40875d8c17f9bbc2.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 95807b808ecce251b57627bd6e13ea913d9741c96df855044f7dffd244e0526c.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 974d7e3faf1e89b62f13e15fe79188ef88021cabb4756c7559e89139b886420a.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 9b0ce93e88462f01af442f042d0be90d893311d46050de09a3cd0c73f87815fa.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 9b3218ef7986d387acfaf258d6d4831480f58c88560d1e5c95d0ad00db86de8a.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 9f7760414784a3eb4e1e47966ff2b532f62828374e17dc7abf5c45969ba4d6fb.
def localCycle00086 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, -2, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a0cf5049d9be685b13561df69059f54fab780291bffc4a972ed775da5bd08fe2.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint a0ec252534b08b739f616296a6d4b0e637ed2082da132b882e86f197cac2f06e.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint a114e10eb331a92b820653a1996f2f2a174684b4cfc3f10d959f62d857ba16e8.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint a33676dd1c3b2b90075efaec3ef4803f74c271a8355810859cef24b356eb08be.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 2, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, -1, -2, -1, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0]

-- Cycle fingerprint a42cc0487cdc7f2a02b40a53a53eca8cc2f6f6e7936c033751c47b989a885c9b.
def localCycle00091 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint aa2b5ae0a68eb39bc368c77dd929bbbebd08d96407d9e349189294991342398e.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint b509d448a7314c88e2878c3728f71169ff23746d0dd697302b7ea2244f01b66a.
def localCycle00093 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, 0, 0, -2, -1, -2, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint b80ca49c478a4b523ab57becfdda7419de7eae122edbd17b147277191d2d8a7f.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint ba7afc5b8f8d9868ad671f51e5885a6c55a09e8bd5a74764fd460c297d232095.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint bec3e80403b2dc863fe4ba8d6ddc46bd78a9082a2ae6024502d39874fa3e7f51.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint bf37c6b8405cc18e092cfca5b64c342ab66bfe2a974dcd28db364a1ab5b2078f.
def localCycle00097 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 22 1]

-- Cycle fingerprint bfa78652b8d54c93dc1b25e2951e6dedcb031744cb758e81cd771b259af7d467.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, -1, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .gapUpper 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint bfcbf09f9e423b554fedf95f1af3c41920429933dfb5a37f2de6e9388d4bafdf.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint c01bd7bad2fd39cf237c77c6b8d79854b9ffa569df713b3c7b3c0daa22b11418.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c166af8ea9a7e47eb5fe9336f170e3f89550b05dd7115a742bac0ae93b13dd13.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint c62a74f8111a44ab213b58d017abbad7d88f2eec4155cf42762fdc44c590241f.
def localCycle00102 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint c9b60c5b61ec3d6558a55a2c13449291bd9f26b527f94adfa12e3e60e7ffc907.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint cc176e496647e9997245839be35a93a4542d0c6b534fc7ff0d49283605d39b4a.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 2, .triangle 24 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint cc4ca043538b67557042ddfb527f6eb8c7c05fb4159ece1e31255769db96ab53.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -3, -1, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint d1752b9746d8c6a4b638a28f4b0f730fac1c0e61272c721377882027d04b27f5.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 0 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d2877a9ce3ea428b80d430c993a2cae32dd567096fe574ec3e8441eccdbc75a6.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 17 0, .triangle 26 1, .gapUpper 3 1, .triangle 1 1]

-- Cycle fingerprint d2e0767068a4c811bd7e40874d1705941f479d12b8b44a63a29ebdd128227518.
def localCycle00108 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint d2e8b588c882a3ec518d6d9b6c116a08add6668d2fbe71aba8b5bc7f00c06056.
def localCycle00109 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint d332106ddbce4eda5486812fa69583473c40efd08f6858793038ce6f2d24b07b.
def localCycle00110 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint d42af62de7a8a2e3e2b1f0c5520c54024089399cb9a7d9a60121d5019e765e1e.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 20 1, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint d66699921845622a987d93a954de60a024071b4a3d638135adc2527e09b282fd.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint d7d50c33698e56fa2d9234109af095295bebbe3bf5f76d636a008c3ff5412129.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint d915a5d47c3f9a2678341592dc5922c5e78eedd404348bb51126af79e6b924a7.
def localCycle00114 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 0 0, .corridorLower 1 2, .gapLower 1 6, .triangle 20 1]

-- Cycle fingerprint dfd318b9403c8af76a6777391919d6cf464e00df578d1ecf63e4020ac7cd6437.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e080d51756b128555d8de290c4d552e52d202808f78b176c049750952486f7dd.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 2, .triangle 24 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint e11aebdb8c202b3164f50c113598273cde22ec77c44b835debf110f03e2ac5c7.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -3, 0, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint e2aa6abfb532088c203ba0f2642b41e79d510eb5f68295c5acb17fca69b24ee6.
def localCycle00118 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint e63ccf5f590b9c08fe0a884986722235f365fe9fcb0a5b65188ca1841b1afb1d.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 1 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint e806202141d3421df68bc8d493c13aa35d2939be227ea7579b2744870232e778.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint e82c10682d30989ce99d1d29319f6d56a4ace17f2d967746981c49f044b12c38.
def localCycle00121 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 0 0, .corridorLower 1 2]

-- Cycle fingerprint e9b55c309dd9f9fdb5fa610bf2043610d8a778a144cf591d9fe987aefaf1e1cd.
def localCycle00122 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint e9e033439713b842dc629d44390de6cd3d8e02e03aa61245ecb57df8710e301c.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .corridorLower 3 5]

-- Cycle fingerprint ea690ebad66241314570e52017e44f156f68cb549751b62bdebf3d7c9882421c.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint ecc88a028dc6aa95830da0ef1d301fc94537382767afe15f1edccc8414a06ab3.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 1 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint edf4d61aaa01c77454fb80084320bfc17519f199caa614b2e4d63edf69b9ad03.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint ee1701b774e34c2353850d14ada54c49a09eac6f92157524280e54e4a9ba1aef.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.triangle 3 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 1 1]

-- Cycle fingerprint f1643d5d4dc9af2f579444272d4a89e3ee02e3413e76c88a785911301ffaf6a3.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint f43dc67368429329024ad2f35688ca5d117e7441c7127378968ab2cb78b54340.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint fae67cda926be77ed51fcca132f3026a8e1bf4f854d129c7ee06c69302cc4281.
def localCycle00130 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 2 6, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![0, 0, 0, -1, -3, -1, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 27 2, .triangle 29 1, .triangle 16 2, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint fd15dcfb4079ba8a13f385f6eb78a46651208f8dec87012e0da05e081f77334f.
def localCycle00131 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 6, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 2, .triangle 4 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint fdf162b872fd4259407bd146072e9c40a511bc1a5ca5cb77ff1040593f4157b7.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint fe493d098a6ca42ec025c6cee27ed4eb7531a97b8b45b1bd409483e7a4b87102.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fe784b05bfd71dc7b318bee4112674bc75ad06c7d0d70d2fafbb159c142dc88c.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .triangle 2 0]

def library : Library := fun id => if id < 67 then (if id < 33 then (if id < 16 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))))) else (if id < 24 then (if id < 20 then (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 22 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 28 then (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 30 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))))) else (if id < 50 then (if id < 41 then (if id < 37 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 45 then (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))))) else (if id < 58 then (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 62 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))))) else (if id < 101 then (if id < 84 then (if id < 75 then (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 92 then (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))))) else (if id < 118 then (if id < 109 then (if id < 105 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))))) else (if id < 126 then (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 130 then (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 16 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13184)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 2, 1, 3, 5, 4], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 0, 3, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 13 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13185)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 124 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13186)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 112 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13187)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 56 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13188)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 50 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13189)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 12 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13190)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 20 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13191)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 7 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13192)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 53 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13193)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 102 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13194)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 102 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13195)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 7 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13196)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 3, 4, 5, 1, 2]], proof := .tail 88 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13197)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 1, 5, 3, 4, 6], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![0, 4, 3, 5, 1, 2]], proof := .tail 7 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13198)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 72 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13199)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 81 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13200)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 1, 5, 3, 6, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 0, 3, 5, 1, 2]], proof := .tail 82 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13201)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 84 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13202)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 5, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 1, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 123 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13203)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 1, 5, 6, 3, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 0, 6, 1, 2], ![4, 3, 0, 5, 1, 2]], proof := .tail 84 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13204)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 0, 1, 2]], proof := .tail 10 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13205)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 0, 1, 2]], proof := .tail 132 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13206)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 1, 6, 5, 3, 4], ![2, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 0, 1, 2]], proof := .tail 126 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13207)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 10 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13208)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 132 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13209)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 1, 5, 3, 4], ![2, 6, 0, 5, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 126 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13210)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 10 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13211)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 132 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13212)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![2, 6, 0, 5, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 126 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13213)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 0, 1, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13214)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 0, 1, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13215)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 2, 1, 5, 3, 4], ![6, 2, 0, 5, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 0, 1, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 126 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13216)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 0, 5, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 124 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13217)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 0, 5, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 112 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13218)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 0, 5, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 56 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13219)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 6, 3], ![1, 0, 5, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 50 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13220)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 1, 0, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 12 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13221)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 1, 0, 2, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 20 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13222)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 1, 0, 2, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 62 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13223)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 94 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13224)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 5, 1, 6, 3, 4], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 84 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13225)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 53 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13226)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 102 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13227)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 102 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13228)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 5, 1, 3, 4, 6], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 1, 0, 6, 2], ![0, 4, 3, 1, 5, 2]], proof := .tail 62 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13229)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 5, 1, 3, 6, 4], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 0, 3, 1, 5, 2]], proof := .tail 81 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13230)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 5, 1, 6, 3, 4], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 84 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13231)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 5, 6, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 84 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13232)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 5, 6, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 84 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13233)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 10 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13234)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 100 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13235)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 132 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13236)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 6, 5, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 126 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13237)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 2, 0]], proof := .tail 10 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13238)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 100 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13239)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 132 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13240)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 126 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13241)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 47 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13242)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13243)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 2, 5, 1, 3, 4], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13244)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 127 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13245)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 112 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13246)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 56 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13247)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 58 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13248)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 12 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13249)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 20 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13250)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 1, 2, 0, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 125 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13251)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 2, 1, 3, 6, 4], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 54 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13252)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 2, 1, 6, 3, 4], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 78 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13253)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 2, 6, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 78 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13254)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 6, 2, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 40 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13255)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 10 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13256)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 5, 6, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 128 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13257)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 83 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13258)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 132 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13259)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 98 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13260)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 89 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13261)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 15 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13262)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 133 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13263)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 4, 3, 6], ![5, 0, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13264)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 4, 6, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 64 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13265)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 6, 4, 3], ![5, 0, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 96 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13266)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 118 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13267)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 38 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13268)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 0, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 119 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13269)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 2, 1, 3, 4, 6], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 3, 2, 1, 0, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 107 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13270)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 2, 1, 3, 6, 4], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 0, 6, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 0, 3, 1, 2, 5]], proof := .tail 11 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13271)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 2, 1, 6, 3, 4], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 131 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13272)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 2, 6, 1, 3, 4], ![5, 2, 6, 0, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 36 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13273)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 6, 2, 1, 3, 4], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 113 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13274)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 109 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13275)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 6, 2, 1, 3, 4], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 103 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13276)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 10 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13277)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 100 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13278)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![5, 6, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 85 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13279)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 0, 4, 1, 2], ![5, 6, 0, 3, 1, 2], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 132 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13280)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 2, 1, 3, 4], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 0, 4, 1, 2], ![6, 5, 0, 3, 1, 2], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 68 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13281)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13282)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 0, 1, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 44 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13283)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 51 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13284)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 22 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13285)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 52 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13286)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 55 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13287)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![120, 59, 18, 105, 66, 65, 60, 43, 28, 25, 122, 75, 5, 2, 19, 86, 108, 77, 99, 3, 91, 97, 80, 32, 114, 95, 70, 0]) }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13288)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 116 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13289)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 104 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13290)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 57 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13291)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 87 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13292)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 4, 1, 2]], proof := .tail 39 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13293)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 1, 4, 3, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![120, 59, 18, 105, 66, 23, 121, 43, 28, 25, 122, 49, 5, 2, 19, 86, 108, 77, 99, 3, 91, 97, 80, 32, 114, 95, 70, 0]) }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13294)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 1, 4, 3, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 61 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13295)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 1, 4, 3, 6, 5], ![2, 0, 4, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 30 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13296)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 1, 4, 3, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 63 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13297)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 1, 4, 3, 6, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 92 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13298)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 1, 4, 3, 6, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 79 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13299)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 1, 4, 6, 3, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![33, 130, 18, 129, 24, 117, 121, 21, 48, 134, 31, 46, 5, 14, 93, 90, 110, 77, 41, 71, 6, 17, 115, 42, 111, 35, 76, 37]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13300)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 1, 4, 6, 3, 5], ![2, 0, 4, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 1 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13301)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 1, 4, 6, 3, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 4 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13302)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 1, 6, 4, 3, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 0, 1, 2]], proof := .tail 29 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13303)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 1, 6, 4, 3, 5], ![2, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 0, 1, 2]], proof := .tail 9 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13304)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 6, 1, 4, 3, 5], ![2, 6, 0, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 101 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13305)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 2, 1, 4, 3, 5], ![2, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 34 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13306)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 2, 1, 4, 3, 5], ![6, 2, 0, 4, 3, 5], ![6, 1, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 8 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13307)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 6, 1, 4, 3, 5], ![2, 6, 0, 4, 3, 5], ![1, 0, 6, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 45 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13308)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 2, 1, 4, 3, 5], ![2, 6, 0, 4, 3, 5], ![1, 6, 0, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13309)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 2, 1, 4, 3, 5], ![6, 2, 0, 4, 3, 5], ![6, 1, 0, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 0, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 73 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13310)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 1, 4, 3, 5, 6], ![2, 0, 4, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 0, 1, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 106 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13311)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13184 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 13184 ≤ id.val) (hhigh : id.val < 13312) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13184)) = true := by
  let j : Fin 128 := ⟨id.val - 13184, by omega⟩
  have hsum : 13184 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13184 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard103
