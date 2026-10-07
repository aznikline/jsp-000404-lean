import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard075
open N4R2OuterLeftReplay

-- Cycle fingerprint 0062319e27108785e7bfcc4b7fbd206316320ac1cc31680169056467662049b1.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 3 0, .triangle 22 1, .corridorLower 1 4]

-- Cycle fingerprint 010111d07bfa528d0081f327719b470bddb2ca9d0a89ccf9a614d4100f38a0c8.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 02af71dbe822a663faf1a3df99d54d87562f9df6b4cda919ca5658e30cd674a9.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 0, 2, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 18 2, .triangle 21 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 04f2650a391a2d0971a8931fe15aea4ce38a11274cf26ca71b4735e5a08725f9.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -1, -2, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 050b75da098fed10dde0cfb63f4b11b7fb0fb4e73fa8ee74b80db59a9484bfdc.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -1, 0, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true, true, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint 0554316a9e098cba7f6e23bb76fdf0b0c3050423c98359ffcf48cfca66a4b031.
def localCycle00005 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 0600f872a79222e82e2d933d364180c74819b65d3051cc01e615651772133667.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .triangle 2 0, .corridorLower 1 4, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 065b77a471e3c88515856bdb968fbd9515aaefd9451a1b0d115812bf24b5af76.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 080db6b07cab995620ae3f8d160f40d23d7ae5a1a4d468c652d8c99b99596863.
def localCycle00008 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .triangle 3 0, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 0ae03e66611c5bfd20f5c2fa28192de09ad86bca70c8094b83836d3c513b4007.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .triangle 21 1, .gapLower 1 3, .triangle 3 0, .triangle 22 1, .corridorLower 1 4]

-- Cycle fingerprint 0c9cc4a3d14b1c2448c12a3bfab0dd9989123a0b52ea369bbff90a8f52972d96.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 2, .triangle 5 0, .triangle 26 0, .gapLower 5 0]

-- Cycle fingerprint 0d8c1f29df5f4053a1992f6c701a4cb7bd868e2e8903db6415c313cb6e38993a.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -3, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0e63936040f76bffbcd7ba6379d37f480f4466e6ec8e3dd28e870b9a3324613e.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 2 5, .distance 2 4]
    constant := ![0, -1, 0, 0, 2, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 2, .triangle 14 1, .triangle 30 0, .gapLower 2 1]

-- Cycle fingerprint 0ef026da17f90eb5a0811ebe29058220d66bca501fce042fb18f570e335aa897.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 12 1, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 1001b98a9e6ba9afe6c974ae25840cec350b97bf131701dbb625150ea9ab1f15.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint 12b16b53326d270c149ec49d3f1b17de635c96dfb6173233eeffc77513cb69fc.
def localCycle00015 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 15677d61800d52044aef84d5def8624959b768bd95c60f17e0819530cc519874.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 0, 0, -1, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 18f33f22046c50c2beea27224a18b234303c38332b19d92dc0bc779429a06f14.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 1bc8c54227af078ea49219659b7616723630e61cb3b46b3109c3ba2b23b665c2.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 0]

-- Cycle fingerprint 1f13aaad5f9d2faa80a63a5569869a6f6cec1ef18e6ed8b1714301fb12599416.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 3 0, .gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 204b88552a7ac0804fbbec2eabda5c29aef8864468e5b3c1cb64db03171adea2.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 209b7bf1ed166aa7e909533f0a3c25626569aaf6be0a0c3a43d70338a2a0e2f4.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 2, .triangle 10 2, .triangle 14 0]

-- Cycle fingerprint 258d8b3d414c702ab2e5bd38397a1e251d9865fcbc4414bcc6eae64d1e23ec63.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .theta 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 4, -1, -3, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 31 1, .corridorLower 3 4, .gapLower 3 6, .triangle 21 0, .gapLower 1 3, .triangle 3 0, .triangle 17 1, .triangle 26 1]

-- Cycle fingerprint 261acdc0edd7d11d2d2477937def62314fff58eb53ebc30cd611fd643da55d72.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 27a934e028c90462b9571d871dda14b2b763fec3d87fbbc98c51df320e45177e.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, -1, -1, 0, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 29a9e48f10f1aca74131243d4e1b358b5db0f78445a12df6ee7a5293d48624b4.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 2cffd3b91420df5bfd8b9e8de0b40929fe054f6b77abc891d852d24b522e7559.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .distance 1 3]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .corridorUpper 1 3]

-- Cycle fingerprint 30055e35ddd3217f4e7374250f8fbd2ab75232e820089b933ee76be3b6997328.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 31acc5e1c82520dc294d2172af81229d2d6cfabb3e38db656acc435b6880c7ad.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![-1, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 0, .triangle 2 0, .triangle 16 1]

-- Cycle fingerprint 3424a70637dbe0059160d60917d6610cca0f6eabe79146750ded65c1931a0001.
def localCycle00029 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 387b867b14c8ab21b0aeb10ab1188766bd2d0a76f99ec414847993bded7d0c4e.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint 389cfe115aaac950d7e96dc07002565ae53d6eb6ba34df6bc7a0780910da1ab3.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint 3947bed2f2d4904a1ee83cc80d7133d617a203006b3b2205e08ab3ce33adb67a.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![-1, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 3a6b7b22c05024ff70ceacedc5f92ca75528832f3c14958c92911b923611db24.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3be2fa798baabb904bed36be9b4b5adbc866074a824866d539fdbffc145c43da.
def localCycle00034 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3c17894cb067e0c76f005bcc56a34a61e1e8e075652a230019dd382ae6c6b6fa.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .gapLower 5 0]

-- Cycle fingerprint 3cd8f30e0ea50adc81086db373d1fe997c1a8970908e6a1370224c7f3cc5d77e.
def localCycle00036 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 3de239ac1416a1ec74125afe840e8e335a447a0b0ca64ce6dbd15793104df3ff.
def localCycle00037 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 3ecb9b4b9c4a0e7ed1eeb186cd60e386fd6df089168d02b0ebfccc3e1856dd49.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 3fc9847bd2db1b066d8725a3c05fdd6960c84ece74d6292c82ec13902f73b45a.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, -3, 0, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 0, .triangle 3 0]

-- Cycle fingerprint 4020135357f3baafbdb1f9958e3de8237bacce9d2a800579d8db2db2527363b6.
def localCycle00040 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 42714df56c55de905048137a75eb802f5d45405480cffa634acf9984249e84d7.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 442027de59d97e0863cdb9747e25c0be342143de35f57cebac1bd63af6c5fe43.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 4470330359762cb614af5e99b9f1a32155c8622c2b1b01acd3c0279f30b24b88.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 4]
    constant := ![4, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 25 0, .gapLower 4 0]

-- Cycle fingerprint 45652f7942d24d03d6ee4ec5af802078d9df3708f43601ed79d4ed2bc390397f.
def localCycle00044 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 462ad52dcad58cec0d14b186b04189aa6339a375b722458bd7da198df129488d.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, -1, -1, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 4 0, .triangle 3 0, .triangle 22 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 488c7e3833018a7989b6b4a85356066ee7123ba47b4b86d99d94509441ae6f8a.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6]
    constant := ![-3, -1, 0, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .triangle 17 1, .triangle 28 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2]

-- Cycle fingerprint 4a230b5232743948a28960e5d8fc1ef9ef87e4a9717bbd14fc4906f972ae2ab4.
def localCycle00047 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 4afed5b7386d02e84e2108b72a77c5753132cfc6ccf2c713710f0eb12630e182.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 4cd72e773dbf5ec3e667e34de8e5d7fc2b8212acdb4d61e20090297e2e6c71ad.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 0, 2, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 4d4d1b0e3041606f55ffac6df881fc340508bce5e30a36f978f210a98db55fb2.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 4dc153a3e07854ea48ed6a83cc416e69f81b389eb6a6748ee795b5b543b52c8f.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 4df54b173b56e55b3897835de7028fb30ef2a016d7789b54c9024ceb5127effa.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 0, .triangle 26 0, .gapLower 2 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 4f4d2b19a3e1409bda3297d806e500b14b3fe311a8960526fea5bbc4d860ccd0.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 4f62ac5034b8ebf62b177df8865cc209c961b25fe0ebacbbe25015ea14e7c2d0.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .triangle 29 2, .gapLower 2 0]

-- Cycle fingerprint 4ffca063c3046e35850a22f39c8f4d079efdebf89a68dd9cf23e50e1be8b24f7.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 536391b0deff43d835d1875405252eaca3d8f21c5f16e31411baada2581c14b1.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 0, .gapLower 1 2, .triangle 17 1, .triangle 26 1, .gapLower 5 0]

-- Cycle fingerprint 541f4c8e1f1eebdd5b7bf92e603c520dcac640b7986a331f4bd56fe3852c6a4f.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -3, -1, -1, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 5455f91991aa95b2d5fa48dea6d063950161498e6d1a9aad6ecbbbcd7cdc3de4.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 5]
    constant := ![0, 2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 12 1, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint 58f83cbc05b9b758dbb4f7b1edca7e0d71539b6ed354dd58987ba4343542b332.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3]
    constant := ![0, -2, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 3 0, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2]

-- Cycle fingerprint 5991e31cb87b1b74d19bfa2596255978f0403bbd5d6d1e800e56b8fba8c116b7.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 5bf05b20c02635766adea6b9361c3960c403764de253a9d8b71e6d6c8ffeb663.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5c19016249922781709f1e123db8e72467e4c36fcaf0de5ded7b448e351a0aed.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 1 0, .gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 5c547877a57e17b0dfa49e2a7e723c1f0035b42136a861cf10acc27d92ada2cb.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint 5cd9b491e9f84ab0a62a4b6d150ec463761f64603178f0d6e98369cea26adbfe.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 5e267a5eecbcdfce3795f0c3fd9a6d8c6630fb9db757670b4bb3cb2c801ce679.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 3 0, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 5fc4306f0f2464996a2df04a3ad805525b8027dbf753e50fb3b550b3cdce5aa4.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 3 0, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 61108bb9959b7324f906a1cd6ce3b56e39a5f934a160266695ca06cd24894f39.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 5]
    constant := ![-1, -2, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 2]

-- Cycle fingerprint 623df791f21f019409dfb24178963c768525f741dafd9bb2fe77dbf8b98d79b3.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 3 0, .triangle 17 1, .triangle 28 1, .corridorLower 2 4]

-- Cycle fingerprint 65f28a112edc56920ac07587ab80063482f3dd566761d338cbf299b3ee7c5248.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 669bff3a8d49aaea725dc4d879e536c4197286ea2592a631a8f636d4f879f042.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 2 0, .corridorLower 1 4]

-- Cycle fingerprint 6722641f89d924f23939be023bb8099f7c2ba4ee2bdb810ccb40a52d18f277b1.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint 6879e6d786b54677f6a756785a600cb9e526213f5629547ac8bfb7cea43fedde.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 2 2, .gapUpper 4 4, .gapLower 6 5]

-- Cycle fingerprint 6a84f4f1de5d823341b02454b218a118c437b8f5e06df725d96b884db44b7d7f.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 32 2, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 6dfde3837efc881bc6fd3747efb5c55c3bfedf3c74a8dde8e2c4729219a73ff4.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6ef4b09001042bf90e96bbdd91d116a852acfb8a1ab83af8d1e6d5bd67ebc2af.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6f3dc7b0d22f522ed941c76ac58a20928afc312e570dfa5acd69ce8bf8c26b14.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 0, 0, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 7158c29affbfbf53c8f07d23b0fb5be579970b9b71ec92484a922ed52020e9a9.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 0]

-- Cycle fingerprint 7258f25259c8c2ad0349f97b534ffcecdcc98ad0cb417f13f331d12e458b49d4.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 72a7dd8d3dbb9fa78af33f25bb332cc6bda66f32b4c78c71ef903841aef59f58.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -2, 0, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2]

-- Cycle fingerprint 74fe2da1a5a6b459bdd393b41cc27bf7afb073681a33525fba15a80d2468f6b1.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 3 0]

-- Cycle fingerprint 755dea2e55d6c248049551b490a74840359be662de9eb14214e329af924ba7cf.
def localCycle00081 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 3 0, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint 76573818b4f57a5be2a087c43676000b591ce25bb93896b9761ae27bbea8a7d2.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0]

-- Cycle fingerprint 767e77925bbc7fd6e1e16ba66985bffcddea67772f9e9c04a51504689ebd0b77.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 7862967a142750ca65f14df688ec684770117ffd2b9aae46da9a15901469cd9e.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, 0, 3, -2, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 0, .triangle 3 0, .triangle 22 1]

-- Cycle fingerprint 7955d28f95cc4436e21ec5ad5739341876a4f0bcb727290eec26efd826318215.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 7a6a5ea1955c756639af554ca19d3f631fc674172c307dfddd6c4877b2a48eb6.
def localCycle00086 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .triangle 2 2, .gapUpper 4 4, .gapLower 5 4]

-- Cycle fingerprint 7bd56a01526c474ae4a4c810e6b276cb7d101f7256ddcd67494a031456de2093.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 7f49c97d8f5af85da4c12ef081b33f5ac714a6eea0778bd2bc5b38a7f0cc28ab.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 31 2, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 7fb512c001725aa91ba6a1906d38a4c2967df3b7235879386886beb8f36f8a53.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0, .triangle 22 1, .corridorLower 1 4]

-- Cycle fingerprint 804987367e106b8a6e53f1be66166338dd49d26762bad14a987bcf425a4f685d.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-3, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1]

-- Cycle fingerprint 829e26e90a1cb70db1ddafb3480d6a592880d880033b8d349e303daa6dda27f7.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint 84bb9e41c2dc6f7ccff2aee83aabf042131c67ededfc640eba3572eceeb27e20.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint 85f40b52e16da9dd76e873a0704e5a83e5312bd757b17c90b620dbc8d187664f.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 89ddadbe2f7b7ee694f21488bfd8b497b7bc9791cdf5c043d82690e0adedccc8.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4]
    constant := ![0, -1, 0, 3, -3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 16 1]

-- Cycle fingerprint 8a12aa9be006de9138e98a93c0d0c7fa7436afc3353ccc69c2f8db1633c4a4ac.
def localCycle00095 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 8a29cfc2bbc2c5178f3d3a59a6e0ba47d6dcf15c01814667f95a2990be43cca9.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 8acca5cf1848ede8dc3e229d8a1961487bdd2256b92714f0dd480b07b20f2b68.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -1, 0, 0, 2, 0, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, true, false, true, false, false, false] }
  origin := ![.triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .triangle 3 0]

-- Cycle fingerprint 8b6e35f4bbe19ddfa67444fbe7af95783dc9015beade3c8609f3c1d3db47ba5e.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .gapLower 2 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8bc2aac716900fdf3944a75d678a9ba1aa557d74ecb605765efeb3d8f93e66b1.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8cd79fc9e0bf6141d973ddb5a50f5e92730899d424428511abe8683f73061f6f.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 8d67ad4fe0b255e351b9f7b93236e1fc3ae0118d1d0e7faff84616a8313ba2b3.
def localCycle00101 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 8e231e0e975a433f2119a6fa6cc1c4ba58a414df34127070c2beba00cac8e89b.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -1, 3, -2, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 17 1, .triangle 28 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 0, .triangle 3 0]

-- Cycle fingerprint 9014655aa37132d3af48564da256a925f0d0df9bfe2019c0985459c973861020.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0]

-- Cycle fingerprint 91cbf0d3153318e7fdaa3693972d0f6ee49248229d093c3b0be19581da9d5fb8.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 926fe6d8689db9e8b5ec74209c68f21e418a667865146304e5bd2c2aa399b6d5.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 2, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 93c36e24bacee3cf975c5914f8ce1bfd89285faae3497e4397d0cb9aa6d6213e.
def localCycle00106 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 947367e40e097c8410e9f4cb829c3297f14ea02e5b380de0ff8d74a0f3fe7e80.
def localCycle00107 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 95fe1e7408c0dae90c56861f072226f502f1fde821b281149edb1d71834fc020.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 0, -1, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 96e139f1ab4405549db2d05e6fc8239530d55813fe61280691436a502a1cbf55.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![-2, 0, 0, -1, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 976a0f4c2c07da7c18b93f7ba7dbf7996ac05351b922026144ec683d5b7c242b.
def localCycle00110 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint 988d0b815f628fd0bdc182320d7c89498225ad97f76f4dd7e21447d8a5932975.
def localCycle00111 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 9c6b26f3c2cf5b5063e0ba66e061c9ba9a13dfafd11703fe4f76629593c9ba50.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint a025abaf1bd4c2a4c506d6ceee610daeef9c7b74dab660ae39f3c35c8fa4f329.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint a0b1b5b133e16424667f77947b1a4e4ba79a7ff2d6b3495144550999bf8f3309.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint a148d87a95081e1f081a3742cd9c8dce126a1729a852ffed3db5e65c6238a56b.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 5, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-1, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 2, .corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint a1641ffd2dfb7aff2628edc98c2d4f3549df1036c5b555710a43e973ca9f2bd8.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, -2, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint a1ba0101e24d47167374985fbc553e578df4e23d55bbb78de7ac16fc3e0c1d9e.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a24887c35f092b435855c135ac93994cbec793e4a48e8984f915217daef00ae4.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a298fc4910a0ab45e515d034dd1f64f6edd51a75faa4581b505263aabd334854.
def localCycle00119 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint a2c856513701c3429fee0b4cfdfe437a01e48ebe2bcb674785ed91da8e88bd41.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, -1, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint a3e56d79e5c6b2cd05deb10a67c57121ec7575ebe6754a715385abfdf83024e0.
def localCycle00121 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint a5a39bd61e34a97eac1d70cde2d5e7d5abdacaa5ac0d5a0ae679cb049970e65f.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 2 4, .distance 3 4]
    constant := ![-1, 0, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 2, .gapLower 1 1, .triangle 16 1, .triangle 25 1]

-- Cycle fingerprint a6b989b733d575cbbeebf00f5b99a9300f44dd96904375656f5115fb6a9a383d.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint a6ca952a1b61eed956ab78e567da903734741b88a52801365bdcc5692594c6c4.
def localCycle00124 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 2 0, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint a7d30b2e6d645ca477b328be57581b10abe37535bb41cb0ff1e7f1f8fbefff58.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint a81d479a2a4008095a2577027380af4112fbd3c43611118d72f57aea023087d0.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint a884cf62cf9a38fb410b20221098e3a91e530cb152cf8d13e42756ca6ce64be1.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3]

-- Cycle fingerprint a96b95be4d9cfe20b2283b01b853ebb61584520fb84f7d6b95829ccaedf67f80.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 0, -1, 0, 3, 0, -3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint aa1a9ca4e3500b4fc478d796c4f1bff1e912e5730868158512b704a8a6ee0a10.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, 0, 0, 3, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 2, .triangle 4 0, .gapLower 1 2, .triangle 22 1]

-- Cycle fingerprint aa607d78664cf93ac167f91a0b2c04a77d92a2dfaac32b0d7726cc6bfebcd6dc.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 5]
    constant := ![0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 12 1, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint abab5a6c9b391273b6b03d3a54bdfc4f02e31d57216b44b15c4b46f98fda3744.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -2, 0, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ac5853d4f673f27035138f76f99e36c60e1b4f06ed83f86c242ac363f122375d.
def localCycle00132 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint aeafff2513ccad27e3f52124cd8e7a01312c760ab37dfe1f3a67b14a71746bdd.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 2, .triangle 2 0, .corridorLower 1 4]

-- Cycle fingerprint aec1392fce0c16b5c8d921ce9979bc16d9774f930208bfdb89e47ea04a5c82d4.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint afa945fababda6482f2985e6f39adf66bf0f62ebf903a44b51c48f5d3a314705.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint b0ae52af2b55199676c41a28eb3cf87cda25071ecbbbb5c4817f237b7644bebc.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 3 2, .triangle 14 0, .triangle 30 0]

-- Cycle fingerprint b0c1a66471ac55a7b3729e6b70d12c118bd9db259bd53dd1093d795ffd12c1bb.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false] }
  origin := ![.triangle 4 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint b0f0298e591a8042e596c6add429cd2b6a59122c6b0c60fdacb59c4b06730081.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, -1, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0]

-- Cycle fingerprint b2a6fc9fe3ce103b30746e71ca02312040af500dab474cccdb794a5f61b0c4b6.
def localCycle00139 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint b3335e8b01bef316ff6d1383917b7b102ddec49419b44a6c87d4590515667fba.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 0 1, .distance 1 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, -1, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 28 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint b4457e1ee4f6564b48aefcf832fec7374a1d66230b00cb10042ecc1fb1297899.
def localCycle00141 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint b575ad32c1e7bfb2899321a2874cc6e2d0abae51ae1dc3b41a8063b140ee3d24.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .distance 0 4, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, -1, 0, 2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 0 1, .gapUpper 4 4, .gapUpper 4 5, .gapLower 6 4, .triangle 21 0]

-- Cycle fingerprint b5c62dc4030709da53a0ad08fbdeb23b05c616ec26a79e068fe3ca63290058eb.
def localCycle00143 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .gapLower 1 1, .corridorLower 1 4]

-- Cycle fingerprint b74f107c73873b04c3c0e16c07fae0312ad6236bf44e5081f1b5800ad4e28879.
def localCycle00144 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 22 1, .gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint b952072cab6e53f53c0dfb6d49a1029897a75575961a08efbbf77370ab0dc92e.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 0, 3, -2, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint bac10f868aa9e26d8193f5944bb60cd431c02d3e2d50693c216b1d1f77790c91.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint bb61edc6976a0ca18370762db210e2a7052e025c844630513fc1af8a5c370c6e.
def localCycle00147 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 0, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint bbd0fc9243a7d7a4193a2793020b56186d7c78cdbd09c6bc6a6a253264ff2023.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -1, 3, -2, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 17 1, .triangle 28 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 3 0]

-- Cycle fingerprint be6fc03193dee59df743e7929a535c5852932ea9c9226ec67c17c2ed0a153bec.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![0, 0, 0, 3, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint be89a47910d46e7de2385e52bc22e693827866d7904d73a0cad4b0ccea796a00.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -1, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, true, false, false] }
  origin := ![.triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint bf944fc5ad9776bd4e33ed3a738ac2ee60c99882d81e30f893f9b5da95df7931.
def localCycle00151 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![0, -1, 3, -1, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint c0a574960195ac02d98ce4670e8b74e7c0d4b7db7e21070bfe0ea27fcc59ccf6.
def localCycle00152 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -1, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .triangle 2 0, .gapLower 1 0]

-- Cycle fingerprint c0e6b0f6ef73974e8220c84ac7bd5b93c8ab5386bf48997f03fcf07b8baab311.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 15 2, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 2 0, .corridorLower 1 4]

-- Cycle fingerprint c1b5b6cde43a9005b0f2f3e0cc1f05672f941b433d759ea955dc6edf87e5922a.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c1cee4c711f1f6145e03e75aaec63cbac59db10e0fb36ace2e8d8ee268b96925.
def localCycle00155 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint c5806d21a3caa182d30328da50b662cea19202dcb6212e52654beff4d6e01b31.
def localCycle00156 : Cycle where
  length := 12
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -2, -2, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6]

-- Cycle fingerprint c67385951ef27e9f00a8c16c68480e985e54eaf3567a4cc98d545452606c8338.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .gapLower 1 2, .triangle 22 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c8e4d39a94190f73964ab339168051d9d6cd60f27982c75f7b2e01cbe8ca8dc9.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5]
    constant := ![0, -2, 0, 0, 3, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint c8edef288d5c6ad61cb070d2443b47091528526e3f52b638bb2b3c48bb96ffd2.
def localCycle00159 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 0, .triangle 3 0, .gapLower 1 1, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint c93071372bd2cefa77316ce3b1dcfc9ebf789ef4273ea54073d0296947195496.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, 0, 0, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2]

-- Cycle fingerprint ca380b8969d236463c8c2e85dd35ac951809f858eeb56d4d144aaacdfd1572de.
def localCycle00161 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint cd6147ed5ba3ab15c8d365aa61e20425f27e57a8715d7e601192598a0ecbe033.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 3 0, .triangle 17 1, .triangle 26 1, .gapLower 5 0]

-- Cycle fingerprint d0aacd0defdc4b377fc8ba0e3b166bdbbfd1a9d4f42ff919d6bca2bf56f1b2fe.
def localCycle00163 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint d34c3d15375d228e5d84430aeebd85643bb69ed9aa961272474d9815de5a2be9.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint d453f9d58f9e3316bd5608c3091bd9e33b917dba14c8a39036dc51ecc65edcd0.
def localCycle00165 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 0, 0, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 24 2]

-- Cycle fingerprint d558bca07d16a834b988f383614f98b6e3fc308b158ac2f26b243794db4ec69b.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6]
    constant := ![0, -2, -1, 0, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 6 4, .gapLower 1 3, .triangle 3 0, .triangle 22 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0]

-- Cycle fingerprint d5c12cf20efb02b50bcda3bf41ae9308d38c9a515c203d9805dae401d908ba8e.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .gapLower 3 0, .thetaNext 2]

-- Cycle fingerprint d605859564b869fb988904c1be332567bb94e9d54472890ef9cf7ff2c378c7c3.
def localCycle00168 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint d7edadc71fc88c779fdbfce41927a3a976365e0caaa60a265d1c77f06c01b109.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 5 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 24 1, .triangle 33 2, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint d867801d4a84352e34103d99033efd9dcf0d0cbaac4adc90b04700d719e9600b.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 0, -1, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint da87ec1759eab3c92da6d2d9e5c7d4ba6ea1e836f383f64a7c1e7bc5301f4935.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .triangle 2 0]

-- Cycle fingerprint dbbf7844d809bb6c0aa1e995533b49ab1aa89391e18436367f01a271f2153e10.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 2, .triangle 5 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint dca7e0c82ee917122dbd5f1f8060dffdc6923054462a37eccfc64b74927ed8ff.
def localCycle00173 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 2 4, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 2 4]

-- Cycle fingerprint ddef4ce07a40d7bbd13be543baa52e82a8de2e6084bf4873df4ac2d5cd2ca277.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .triangle 21 1, .triangle 20 2, .gapLower 1 2, .triangle 2 0, .corridorLower 1 4]

-- Cycle fingerprint de244583924c711e73a2c925e4feb3ee0eba94753ac355e5f8849662406e1280.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint df9778b3eada686e7873489f9db489c7dc2c3b62aa46dc2cf7f22ddf49245f19.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .triangle 24 2, .triangle 4 0, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint dfac72f17d6c349b48286414bb7d22c70d178d67df4912ee72f41b1ed4cdd46d.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 2, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint e09e5a64fc5469f79d419c5e9cbecb12a5b433597b059de4f6ab35177f7dd69e.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint e45713c9ff16a9b9d6fff811dec2efe2b8bf4b282a0bf072f8ac795d1ac0d048.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint e4841d8ffbb8d6ca8c142f408f35fbce38734414acd5519c0b95cba641772d2e.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 0, -1, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 1, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint e5c340d4e14d50aea514754b10946a6d1007aa88303565aa5b16da65fb110723.
def localCycle00181 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint e7dad80b86c25b7304bcc73ea7cd1e996efcde05c7b76c5ebab6fb54be0f836a.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3]
    constant := ![-2, -1, -1, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 3 0, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 6, .triangle 15 2]

-- Cycle fingerprint e97f3b41ce43002dd93db4fe5ef37f0b300de41c8f2de87259cca7902f2165bb.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 2, .triangle 12 1, .triangle 13 0, .triangle 34 1, .triangle 33 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e9b14b10b9aa2d7e96a6269c317926f9c345cf55abeba2b002b5503017ecc080.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 20 2]

-- Cycle fingerprint eb0def25e72d590cf496bf931683500eb17acbf3d5ce83a053a88d793c2f0882.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5]
    constant := ![0, 3, -1, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 5 0, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2, .triangle 17 1, .triangle 26 1]

-- Cycle fingerprint ec8c8efc30dd907efed0f24576dc4ef135e7417c38fe8b02186f528c1e6c004c.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint ee31d4ab911edf2e71a3da7b6620c0b4fb58c298a4435deb9b9dc03ba6d839f9.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint f12fe4520a400d8d3813ed4e77b986c771d293d85c13b1c98c9b387e64d24bcc.
def localCycle00188 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 2, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint f32bc52cdbae62baa1fc82b91922b36b23964f34afd6e3360de99f065d085310.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 0 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 8 1, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint f363b0fb3dd13ca8a313e9c85d1b23b6067caa4b2366972ea25dea993ed9f2ac.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 22 1, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Cycle fingerprint f5f076a2e60ee8603255216045891b2fcd825de561b08243a4129e3ec3f1beb8.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint f7c14d101912707f762898765c692f83c379d0ab9fd00760971e0c0fc19fca3a.
def localCycle00192 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -1, 0, 0, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2]

-- Cycle fingerprint f802c4210e04f179fbce723da85f54dd2f57eb84f73f0676a62ae385f4c3c4bd.
def localCycle00193 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![-2, -1, 0, 0, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 20 2]

-- Cycle fingerprint f9067ba4b4b2d8b9d68d4874a95d3ff77c5ec193f14e00d64bcacc3da85ad917.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, 0, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 22 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint f9268c627256f1cdc0b50f26881cc273297f347427ec02138b1711d28cabdf0a.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 3 0, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 4]

-- Cycle fingerprint fc1151bcd2949019397b88757cb44ef7f00933ca75a9301a2a6fd7566bc57311.
def localCycle00196 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .triangle 28 0, .corridorLower 2 4]

-- Cycle fingerprint fc6771a70a0b0b19c8998462cbbf44f0d7bca83f62ad6e5189048e4c8bfe3533.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint fceaeda0b3e10879ffdcf1a8245465033df60e5302e71bb59fb88d83ee671708.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint fd20e562c5bfa57e102de588482f9ea86b70295349a7cb98c350670d8392c4ef.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 15 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .triangle 2 0]

-- Cycle fingerprint fdd34c7616a0478a6b4adf47d39001fdbe9701f63fac8a2818e9a711539c04b4.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint fe04af34b89992bcd2d16b8051bb3f1c435a7ecf5893d81dd0521bd56bb279ab.
def localCycle00201 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint ffa72d90344d5d2826297714a2309592964b1babffa6d0b1e50d7084c9975c24.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6]
    constant := ![-2, -1, 0, 0, 0, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .triangle 17 1, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 2]

def library : Library := fun id => if id < 101 then (if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 88 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))))) else (if id < 94 then (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))))))) else (if id < 152 then (if id < 126 then (if id < 113 then (if id < 107 then (if id < 104 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 110 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none))) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))))) else (if id < 119 then (if id < 116 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)))) else (if id < 122 then (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))))) else (if id < 139 then (if id < 132 then (if id < 129 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 135 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))))) else (if id < 145 then (if id < 142 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 148 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none))) else (if id < 150 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))))))) else (if id < 177 then (if id < 164 then (if id < 158 then (if id < 155 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))) else (if id < 161 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))))) else (if id < 170 then (if id < 167 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)))) else (if id < 173 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))))) else (if id < 190 then (if id < 183 then (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)))) else (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))))) else (if id < 196 then (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)))) else (if id < 199 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none))) else (if id < 201 then (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 1, 0, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 92 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9600)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 1, 0, 5], ![6, 2, 3, 0, 1, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 52 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9601)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 1, 0, 5], ![6, 2, 3, 0, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 188 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9602)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 5, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 189 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9603)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 5, 3, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9604)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 5, 6, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 154 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9605)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 1, 5, 3, 6, 2], ![4, 0, 5, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![37, 114, 86, 142, 132, 94, 70, 149, 83, 123, 116, 145, 152, 48, 78, 62, 44, 143, 156, 193, 131, 174, 198, 96, 2, 25, 6, 24]) }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9606)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 1, 5, 3, 6, 2], ![4, 0, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 154 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9607)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 1, 5, 6, 3, 2], ![4, 0, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 99 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9608)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 1, 5, 6, 3, 2], ![4, 0, 5, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 0, 1, 4, 6], ![3, 2, 0, 1, 4, 5]], proof := .low (![134, 103, 86, 64, 57, 201, 70, 67, 83, 17, 3, 32, 152, 48, 120, 79, 121, 143, 51, 76, 192, 153, 199, 100, 49, 47, 4, 124]) }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9609)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 5, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 10 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9610)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 5, 3, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 75 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9611)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 5, 6, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 154 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9612)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 1, 5, 3, 2, 6], ![4, 0, 6, 5, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 6, 1, 4], ![0, 2, 3, 5, 1, 4]], proof := .tail 117 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9613)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 1, 5, 3, 6, 2], ![4, 0, 5, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 181 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9614)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 1, 5, 3, 6, 2], ![4, 0, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 135 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9615)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 1, 5, 3, 6, 2], ![4, 0, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 173 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9616)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 1, 5, 6, 3, 2], ![4, 0, 5, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .tail 135 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9617)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 1, 5, 6, 3, 2], ![4, 0, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 6, 1, 4], ![2, 3, 0, 5, 1, 4]], proof := .tail 117 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9618)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 1, 6, 5, 3, 2], ![4, 0, 6, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 0, 1, 4]], proof := .tail 105 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9619)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 1, 5, 6, 3, 2], ![4, 0, 5, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 1, 6, 4], ![3, 2, 0, 1, 5, 4]], proof := .tail 34 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9620)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 1, 5, 6, 3, 2], ![4, 0, 6, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 0, 6, 1, 4], ![3, 2, 0, 5, 1, 4]], proof := .tail 197 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9621)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 1, 6, 5, 3, 2], ![4, 0, 6, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 0, 1, 4]], proof := .low (![37, 139, 72, 28, 26, 21, 70, 119, 184, 126, 136, 176, 152, 150, 180, 19, 121, 143, 27, 165, 160, 133, 171, 177, 12, 30, 38, 124]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9622)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 1, 6, 5, 3, 2], ![4, 0, 6, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 0, 1, 4]], proof := .tail 172 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9623)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 1, 6, 5, 3, 2], ![4, 0, 6, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 113 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9624)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 6, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 169 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9625)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 6, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 1, 0, 4]], proof := .tail 91 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9626)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 6, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 1, 0, 4]], proof := .tail 172 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9627)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 6, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 113 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9628)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 1, 4, 0]], proof := .tail 41 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9629)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 1, 4, 0]], proof := .tail 41 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9630)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 1, 4, 0]], proof := .tail 85 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9631)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![4, 6, 0, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 1, 6, 0, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 163 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9632)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 6, 1, 0, 5], ![3, 2, 6, 0, 1, 4], ![2, 3, 5, 4, 1, 0]], proof := .tail 92 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9633)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 1, 0, 5], ![3, 2, 6, 0, 1, 4], ![3, 2, 5, 4, 1, 0]], proof := .tail 92 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9634)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 6, 1, 0, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 2, 4, 1, 0]], proof := .tail 92 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9635)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![4, 6, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 2, 6, 1, 0, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 92 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9636)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 6, 2, 1, 0, 5], ![3, 6, 2, 0, 1, 4], ![3, 5, 4, 2, 1, 0]], proof := .tail 61 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9637)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![4, 6, 5, 2, 0, 1], ![3, 6, 2, 1, 0, 5], ![6, 3, 2, 0, 1, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 61 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9638)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 4, 1, 5, 3, 2], ![6, 4, 0, 5, 3, 2], ![6, 4, 5, 3, 0, 1], ![6, 4, 5, 2, 0, 1], ![6, 3, 2, 1, 0, 5], ![6, 3, 2, 0, 1, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 187 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9639)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 141 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9640)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9641)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 95 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9642)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9643)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 95 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9644)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 5, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 186 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9645)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 111 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9646)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 74 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9647)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 95 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9648)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 33 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9649)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 95 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9650)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 5, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .tail 43 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9651)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 5, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 87 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9652)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 5, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 87 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9653)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 155 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9654)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 146 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9655)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 1, 0, 6, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 0, 4]], proof := .tail 127 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9656)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 95 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9657)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 4], ![2, 3, 1, 5, 4, 0]], proof := .tail 183 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9658)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 6, 0, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 1, 4, 0]], proof := .tail 146 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9659)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 1, 6, 0, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 1, 4, 0]], proof := .tail 127 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9660)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 1, 6, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 13 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9661)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 6, 1, 0, 5], ![2, 3, 6, 1, 0, 4], ![2, 3, 5, 4, 1, 0]], proof := .tail 7 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9662)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 1, 0, 5], ![2, 6, 3, 1, 0, 4], ![2, 5, 3, 4, 1, 0]], proof := .tail 190 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9663)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 190 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9664)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 1, 0, 6, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 55 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9665)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 1, 6, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 55 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9666)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 190 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9667)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 98 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9668)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 1, 0, 5], ![6, 2, 3, 1, 0, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 178 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9669)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![4, 5, 0, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 101 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9670)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![4, 5, 0, 3, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 118 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9671)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 107 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9672)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![4, 5, 0, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 118 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9673)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 107 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9674)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 107 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9675)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 88 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9676)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 5, 6, 0], ![2, 3, 1, 4, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 73 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9677)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 5, 6, 0], ![2, 3, 1, 4, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 104 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9678)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 6, 5, 0], ![2, 3, 1, 6, 4, 0], ![2, 3, 1, 5, 4, 0]], proof := .tail 179 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9679)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 1, 6, 5, 0], ![2, 3, 6, 1, 4, 0], ![2, 3, 5, 1, 4, 0]], proof := .tail 36 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9680)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 1, 6, 5, 0], ![2, 6, 3, 1, 4, 0], ![2, 5, 3, 1, 4, 0]], proof := .tail 1 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9681)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 1, 6, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 2, 3, 1, 4, 0]], proof := .tail 107 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9682)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 6, 1, 5, 0], ![2, 3, 6, 1, 4, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 18 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9683)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 1, 5, 0], ![2, 6, 3, 1, 4, 0], ![2, 5, 3, 4, 1, 0]], proof := .tail 18 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9684)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 2, 3, 4, 1, 0]], proof := .tail 18 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9685)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 1, 6, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 3, 2, 1, 4, 0]], proof := .tail 191 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9686)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 18 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9687)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 167 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9688)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 31 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9689)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![4, 3, 5, 0, 1, 6], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 164 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9690)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9691)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![4, 3, 5, 0, 6, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 5 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9692)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 1, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9693)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 0, 6, 1], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 5 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9694)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 5 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9695)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 63 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9696)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 1, 6, 0], ![2, 3, 4, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 20 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9697)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 1, 6, 0], ![2, 3, 4, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 112 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9698)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 6, 1, 0], ![2, 3, 4, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 196 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9699)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 6, 1, 0], ![2, 3, 4, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 42 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9700)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 5, 6, 1, 0], ![2, 3, 4, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 69 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9701)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 5, 6, 0, 1], ![3, 2, 6, 5, 1, 0], ![2, 3, 6, 4, 1, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 175 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9702)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 3, 5, 6, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 5, 1, 0], ![2, 6, 3, 4, 1, 0], ![2, 5, 3, 4, 1, 0]], proof := .tail 14 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9703)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 3, 6, 5, 0, 1], ![4, 2, 6, 5, 0, 1], ![3, 2, 6, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 2, 3, 4, 1, 0]], proof := .tail 5 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9704)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![4, 6, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 2, 6, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 3, 2, 4, 1, 0]], proof := .tail 5 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9705)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 4, 3, 5, 0, 1], ![4, 6, 2, 5, 0, 1], ![3, 6, 2, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 54 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9706)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 4, 3, 5, 0, 1], ![6, 4, 2, 5, 0, 1], ![6, 3, 2, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 60 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9707)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 189 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9708)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 75 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9709)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 154 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9710)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![90, 71, 115, 22, 132, 11, 29, 53, 157, 158, 65, 45, 144, 151, 23, 8, 159, 15, 93, 138, 40, 110, 170, 147, 9, 102, 0, 137]) }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9711)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 68 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9712)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![4, 5, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 99 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9713)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![4, 5, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![3, 2, 0, 1, 4, 5]], proof := .low (![90, 81, 161, 46, 128, 140, 29, 80, 82, 59, 194, 84, 144, 122, 109, 182, 50, 15, 200, 16, 106, 110, 108, 202, 89, 148, 97, 66]) }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9714)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 2, 6], ![4, 5, 3, 0, 1, 6], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 162 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9715)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 3, 6, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 75 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9716)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 5, 1, 3, 2, 6], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 0, 6, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 2, 3, 1, 5, 4]], proof := .tail 154 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9717)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 3, 6, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 1, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 35 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9718)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 5, 1, 3, 6, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 0, 6, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 68 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9719)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 5, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 3, 0, 1, 5, 4]], proof := .tail 99 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9720)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 5, 1, 6, 3, 2], ![4, 5, 0, 6, 3, 2], ![4, 5, 6, 3, 0, 1], ![4, 5, 6, 2, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![3, 2, 0, 1, 5, 4]], proof := .low (![39, 77, 56, 58, 128, 140, 29, 80, 129, 166, 194, 84, 144, 151, 130, 182, 50, 15, 185, 16, 106, 110, 108, 202, 89, 148, 97, 66]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9721)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 5, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 168 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9722)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 5, 6, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 3, 1, 0, 5, 4]], proof := .tail 168 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9723)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 6, 0, 4], ![2, 3, 1, 5, 0, 4]], proof := .tail 125 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9724)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 6, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 0, 6, 5], ![3, 2, 6, 1, 0, 4], ![2, 3, 5, 1, 0, 4]], proof := .tail 195 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9725)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 4], ![2, 3, 1, 5, 4, 0]], proof := .tail 13 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9726)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 4, 5, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![4, 5, 3, 6, 0, 1], ![4, 5, 2, 6, 0, 1], ![3, 2, 1, 6, 0, 5], ![3, 2, 6, 1, 0, 4], ![2, 3, 5, 1, 4, 0]], proof := .tail 195 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9727)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (9600 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 9600 ≤ id.val) (hhigh : id.val < 9728) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 9600)) = true := by
  let j : Fin 128 := ⟨id.val - 9600, by omega⟩
  have hsum : 9600 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (9600 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard075
