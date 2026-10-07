import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard133
open N4R2OuterLeftReplay

-- Cycle fingerprint 00b50151e76365d040e5136578a132bb0fa74f9798238aee7a3715dc7796a8b0.
def localCycle00000 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 00de56bcc72aa532820d4310fa81ff1599824b337ca5e63a6c47f0717c3bec79.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 035eeb8438f4df10824a671a3e0fe50d281ae3fa1a09b66a1b573d66a1706ae8.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint 038706c0f0ba57022d8fdd5e2823c0432d55f4381d3ab748400d59f62752231a.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 0, 3, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 03f13ba4f51df9347f61b3bde7ab05aad6c0731192b8a66e8bf4864434d7cc92.
def localCycle00004 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 05942d5961c856f2df5bbb7d1f78c00089e3e0e4fdaf1f629555aaac91c64a62.
def localCycle00005 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 07a7f6ebd377f1fa945f73d928cdc2d634164072885d8b8a1ce0df1323fc4e24.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 07c30b940439d84700f636fff934b65fe350b3f986d8fd278cb802b0415db744.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0838dbd0a4f677077796d53a6f0579c7d9eece7793454c25fbac91acc3d7e8ce.
def localCycle00008 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .gapUpper 5 2, .gapLower 6 2]

-- Cycle fingerprint 08e2993d2f03b711ea429950c860838b4f634cb190657b89212913758945a202.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1]

-- Cycle fingerprint 0995f402c1e20498e6a804bf2bb427b87bfe8879aa26378dc6dd4c540964dcd4.
def localCycle00010 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, 0, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 2]

-- Cycle fingerprint 0fd60db1a9842a61b30fba5d55b4e35f313098d4ac027271e51ad09685fcf340.
def localCycle00011 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 11a754d7fb529bc10bcb50b2542e1aab8ec6d41bce2648cc358a8e4b2f935c02.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 12e21d60bbc1e152fedbb58304ea33c91d2d1b70e7c6ce8acfff93cedfda13a6.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.triangle 6 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 5 1]

-- Cycle fingerprint 1334a6052802868b69fe21ed79e069a6f14456efde0fd3dad8865d1e609bd056.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .triangle 4 0]

-- Cycle fingerprint 1427094b6660155fcbe36c299910cdbe610253fca39e8c9ef324d79da85c7d49.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 15dba8cd0163e10695cee32e40e64dd96f17c71a045eee49c560914ca47aa682.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3, .distance 3 6]
    constant := ![0, -2, -1, 0, -2, 0, 0, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 2 0, .gapLower 2 6, .triangle 27 0]

-- Cycle fingerprint 168473d30e7b9f3fa321a6035307b121826110fdb7e54873b7f9710717ee3d4c.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 185aa089cdc52d155120ca6957f2f5f6f6c161384cefac672f308ec841ceaa4a.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 1aa2f73c6abfb56f628c27793016302ea173663702376a3364e40f58f5ee8a66.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 1af553946c71b1e55a830216841b918b7dca668937208f122174f0ff22243b9e.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 1b333bfe770062482b5f51a60f644b605d7181b2b01a6f8365a7d3520a81bd19.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true, false, false] }
  origin := ![.triangle 6 2, .triangle 12 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Cycle fingerprint 1ddbf97364a4dcc2b4111aac89440a182ba9d374e478112311f1d5b3e1298d1f.
def localCycle00022 : Cycle where
  length := 17
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, true, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 1de0343847aebf095e452688b6bc631eb821c515d728036fe8c2f5f13dc0a9f8.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 1e8fc2d9b23ef719f48c1bfa6b67a750e83a17e2b7de3c61c00c8d46a1a361a2.
def localCycle00024 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -2, -2, 0, 0, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 6 2, .triangle 4 0, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2]

-- Cycle fingerprint 1fba4bfa5c8813c3ad99c991616d1075715e26b5958ccd38a7ad3ea68e383f3b.
def localCycle00025 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false, false, true] }
  origin := ![.triangle 28 0, .triangle 34 0, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 1fffd01d8e959654a73a04d699cb0e8c8d143db7a49f60a60fdcbced43b1858b.
def localCycle00026 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Cycle fingerprint 231b708a381e2354bd92fbf338b90fe458446c17b4ab2ae495b68d1ef77506fd.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 10 0, .triangle 20 0]

-- Cycle fingerprint 235f430e7594acb9eb48e502d0c4b7836e507f8f7c9385194ceafddb80b0f047.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0]

-- Cycle fingerprint 268e54b72ca37573dd31442f613e38c273a02d8533758e6bf92449a284a56b76.
def localCycle00029 : Cycle where
  length := 14
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 26a16be1be20865d3248f083c8c6692238f080824f03a5b64c086e883074aecc.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 5, .gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2]

-- Cycle fingerprint 29afff7b69b0c739e6020d31c7db2802c184cc2facd9aa0f57b3be44e00b882c.
def localCycle00031 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6]
    constant := ![0, -1, -2, 0, -2, 0, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2]

-- Cycle fingerprint 29f9930d47706fa2a3585318192f7cd1658f6ffce4f25e9be6a944e4df36d17a.
def localCycle00032 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6]
    constant := ![-1, -1, -2, -2, -1, 0, 0, 3, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2]

-- Cycle fingerprint 2a99ecd236abb408ceac781c49a4ad2afb0eae4eea22ff1401efe7e35888ac8d.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2b4d8ac667e2c34a6da75f0c4357fbab6db8f91bdb57a84ea6c21f06f2d1b8c9.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 2c4f56e2ce1ef2da953ecef0dc134946cb18bbf43e814f404f49d3179db50986.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, 3, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 2cb39d5c9d7c24a58270f7cd1e5390d7f36bbbf02c6556513195decc6876b33e.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 31584f839232370cbfa120d1013a24930c40bedd88dd8dd572e992a1652c5b7b.
def localCycle00037 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6]
    constant := ![-2, -1, 0, 0, 0, -2, 0, 0, 3, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2]

-- Cycle fingerprint 34404c5880cba8e5d1c90ede98e8f63e314a574d4625501b229a8a5762c1c53d.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0]

-- Cycle fingerprint 355428bfe9eb8dd0f42c9435f0b2fac19e63d788c759a0803e3b3f4b016de93a.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6]
    constant := ![-1, -3, 0, 0, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 4 0, .gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 2]

-- Cycle fingerprint 37fa87249c5473161dafcaf88f3afcf6d258519f01312aff20fa96cc21cb5198.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -2, 0, -2, -1, 0, 0, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2]

-- Cycle fingerprint 396966649d3c92c7bbdf7d1903afdedad32f1c186402f65339e24c578bf19aa1.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 3c97c9069fa7ea5b598d9fbf53e7e0d22da9fb3805902e8d2382d5b18a668d69.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 3c9b58cc536e5d33168f272e0b9ce30ddeeb4babe22a40d4647b00f09aee7dc7.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .triangle 22 1]

-- Cycle fingerprint 3cc4e305cbc91f099afc70c17f2c2f7e2f7a885c5dd08ba655c79b174799d48e.
def localCycle00044 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 3e2e67053e7b6c0c13f405e05fbd84e08bc7e7859e0f7a48902ce8da5f61fbd7.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 4 0, .gapLower 0 4, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 3e8b3d6b7c555f90e01cafc3246e90e696e871bb82f38f09a18fd66b84e20278.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 3eacdadbd742648a1db99659e6d128a2307cd5dcddc63d953308296bb467f8f2.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 4306796dd734d5da601a1644866909bf6ed10441ba36d1c59ca7574d5aa4a90e.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 430689c0504c24512b789d197b7a45633495b53570185e7190074d9d9a07a010.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1]
    constant := ![-3, 0, 3, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 2, .triangle 4 0]

-- Cycle fingerprint 4640637b3485742c5da251fb23b0ba7f2688f44ca589e3699c066709fd42703f.
def localCycle00050 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5]
    constant := ![-1, 0, -1, -1, -1, 0, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2]

-- Cycle fingerprint 47f5436a19b51e0da9ad3aeee762a920eac630f7fc2554638af252e5978d9d2d.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 48315a4f82125c98adb8ff9e4b90ca9dc8fdfaeaeacf85602f4a21e3c34a123f.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1]

-- Cycle fingerprint 48525826fd2d2175ac3a6f150858d4080876434141e0ad678ba872296d7f714a.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 4a452cbde8baa9f0adc57e5bc665a1f6c7b6513809c023a0e4661ea0bc85b46c.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 4a60279a4b09b776da551768da57d349ca6f57ea54cfc407b4fadffa14ff31f7.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 3, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 4c3922fd7fdabc73c8c042ff833147d956d4b146c4f919dc69868ad78018986b.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4]
    constant := ![0, -1, -1, -1, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2]

-- Cycle fingerprint 4c501302858ff0cc96318a4038d86e1dc4d35dbd28311538baae0a4d9b7d4ab0.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![0, 4, 0, -1, 0, 0, -2, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, true] }
  origin := ![.gapLower 2 0, .gapLower 2 6, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 4d1661038617402b2f228fa20e84262e6701cd94120f4fab24bc60115315c84c.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 4e93a8e183c84a036af805c278cacf0d60d88ae84600439d6c1485f102d9f913.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero, .theta 6, .distance 0 6, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5]
    constant := ![0, 0, -1, 0, 0, 0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, false, true, false] }
  origin := ![.triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2, .thetaUpper 6, .gapUpper 6 0, .triangle 4 1, .triangle 1 0, .triangle 15 1, .triangle 17 0]

-- Cycle fingerprint 4f85833a6219e71a4d414124653aa0d1315dcb241b7cd90a1fa8531e9bebeeaa.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 4fb133eb1f42e51811c4de396993910ce305401b4c7a5690de2916e56bd87931.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 4fbeb56ecb52f5ecb20465f0b011255ea7fc4ed4b011c576c0a5fb43fc622c0f.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 50a1d092001857c987d413e882139fafaf6341eafd27083cadbf56df1c76f020.
def localCycle00063 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5]
    constant := ![-1, 0, 0, -1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 33 0, .triangle 34 2, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2]

-- Cycle fingerprint 52efade9ab938987ae83d90c2cb855b341130d311829a1321d72f2ab6b90e817.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 533e83157b779b3fd56834db0967fa0c70e66124b9b8aaf06703f5f7a4452c8c.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 20 0, .gapLower 5 0]

-- Cycle fingerprint 53b6a33185d4b20cb6c34a442fed235738a916b7df527e9d4080bd93c945af25.
def localCycle00066 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, -1, -2, -2, 0, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 53ea8c6119f1a6e9518652dcba9539beeb3d39385c0988607fa7623d19fec855.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 5432c6f6a0c5f335d0c48dd1a2574adb6bda3743ed34299f0e93fd55b9ad4ec4.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 558c91fddf368a6017407dc14f3a97b9b8295752e184cea8fa4bbc74c3b6e02a.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, -1, -3, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 58de7fa297f4d630299f289e397d645a35509cdf95265c62c922a4b94fbea5cd.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0]

-- Cycle fingerprint 5a199d94810ebcefc0196b1c43b86b1d0a428774f0934971984268aa12808ced.
def localCycle00071 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 5a2bd2487fab1c65aa261e27d553c3490a4184c0e99154e786509a3105e2c147.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .triangle 22 1]

-- Cycle fingerprint 5ab4a37d07d844ad94fe145bd1079153ab6e0db84fa49cca49c173467493c980.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0]

-- Cycle fingerprint 5c097f5ddb0bfac562e97851537830f6f981c38c4e20124478f68a0bb841ec47.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 5ebbefc98f9dfb9149fc739ec6ef7112b5bbb76c1b22b618edf699a49c332ca6.
def localCycle00075 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, -1, -2, 0, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 5f5f4bd590f2e4b46204dbaebe447cde591f3b9b039179d9dc25145044647d1d.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 5f5f852e9f6ab8dbbe8f67d660a58fab0bf8f49f9d6eaafe6763abf5a649ab47.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, 3, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .gapLower 6 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 627bc692b12051cb442ef9a5affa3ce2e825f868658afbdd0f6a76606d851455.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 628084c4907c5779ac07ff328e64a2ae9ec21b2139773cd8a3b5fbf18d582d6d.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 63a5e0449e73babe952a75b669dcf31999c465a560b6465bafffeb0d02bc962c.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 6705caf71579e2b59007412a6ea8ad8dd31728f608b3ff39e21494323f79ac4a.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 2, 0, -3, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 6848250362c2d6de9277e320a9e69d21c04bc1384832ec4adbc5ae13f3aacf96.
def localCycle00082 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, 0, -2, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 68ad549a1b2160b714342b3d149079e52486df72ff75980eabbff896fb428aea.
def localCycle00083 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -2, 0, -2, 0, 0, 0, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, true, true, false, true] }
  origin := ![.triangle 23 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2]

-- Cycle fingerprint 6ad33e497ce739153a869d9185601f594ec9719e912669da2eaccf6138c925f8.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6c37d2193ef94e4c714bac87a93980abc53c2cfdcf3096416556f2a6e407cc2a.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6]
    constant := ![0, -2, -1, -2, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2]

-- Cycle fingerprint 6cdb5dfc195c5b6fede2d6cd80e55b4eb38f23662952c5a10493281cbc71c224.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 6e1db01abb8c3ed8c1d9882698a63416cc10610d5224d73d765ba86cf217ff88.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![-2, 0, 3, 0, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 6f0aadcfc48bff1397ca41582f31101a267c64a9af40032e23e15503269c53dc.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 71a3f10ac4949bfafb1b043b239ab836e8a2e8d55cefeb268088f67ba2532694.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6]
    constant := ![0, -1, -2, -2, 0, 0, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, false, true] }
  origin := ![.gapLower 6 2, .triangle 4 0, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2]

-- Cycle fingerprint 7245d5f88be066eeb37fbbdf4ac826d8c729d7ea5b89c2e47501f98af60b1d63.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 72b6b82bf08dc9d2b0dd45a9d2ffa040667edca9881d4ed02187ac2c42b7f967.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 738f2c9739a9447691859db859a455504d3fed51e2141e969f547662571c3582.
def localCycle00092 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 16 2, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaLower 2]

-- Cycle fingerprint 73adad1c0415a0b7c1683bde72b97b015ef73edff1e2966b84f5468fdc39ba75.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7453005a6c6a3f4d65a519304e07153859e3f9840259d9ef60330dac1d7a51d1.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7655d3f80e256d0c60660743ef657dafa38948c98de1ab2ee96f638c0eb32d87.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint 77ae28fcceb2b82bd005ce647cc279eee53062162152d8879d198b2f2bd2af49.
def localCycle00096 : Cycle where
  length := 13
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 33 2, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 77e2cf3f82cac83f91a5d06792c7ca690467dd784f783d0e72d0e72af753a71a.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 78beaf4a60e19f5b8047c26c8ebf4001597f0cb2d3817af0e0e7c07d0931495d.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .gapLower 4 0]

-- Cycle fingerprint 7978411700430e2b705a11430a22e82bca2a09bae5a171c919bd363250629241.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 79e816a4607f31462e740560d0c09569800075b484659d1a2cc189de682baec7.
def localCycle00100 : Cycle where
  length := 13
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6]
    constant := ![0, -1, -2, 0, -2, 0, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 7a2dbbf2ab89a467f6ae7244d2964848645cc315e0ed421335076225912e5d16.
def localCycle00101 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 7a2e050dfe84d9f565a73f635478dba5b00ec2743b11234347cf812652ffd9d4.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7b2f82e2c01052be4364a7c960f234cb5dd278cc238e3ba1d770e60b829d1980.
def localCycle00103 : Cycle where
  length := 13
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![0, 0, -2, -1, 0, 0, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, true, true, true, false, false, false, false, true, false] }
  origin := ![.triangle 34 2, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 7b8655fbd6a84914529721e95917deb0c96fdf53a0e340a8dca13e1f9b0a000d.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, -2, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .triangle 22 1, .triangle 19 1]

-- Cycle fingerprint 7c8a1f6a5cc1cd65232b11ee1a648b569c6242dabe4cbacbafed1afe3cdfa2c8.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 7c9819791ded06f8dc12c455a696bc05c8b323ac8b5886dd6bcd9b5de7a298ed.
def localCycle00106 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 7ede6687d09d7380b2969e39f3ec492cd29b3e3b05190bd84a42c6ce30b6b64d.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, -1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 81829c111280f7144b1f51129d94b7f6f339369e3127f1677530ce8cfd9a62df.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 5, .gapLower 1 4, .triangle 22 1, .gapLower 4 0]

-- Cycle fingerprint 81bc666f00c308c09ce9fb779b3852888052f0c78b5de7fa996ffb581c965fa7.
def localCycle00109 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 13 0, .gapLower 0 3, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 83f2a3db22d32007c8108659565898cecac19210ef06f4e30036d0d472a797f9.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4]

-- Cycle fingerprint 86cfa28ac3b35ca96e8d6899c6160f9005e4bf165f1e793fbfc66c2068b8d41a.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 887de81404db7378f293ef9b59694a1231cfd7ef57af94d47713543a753dfdf5.
def localCycle00112 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, 0, -2, -1, 0, 0, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 8ac7b0237c7d09630c5adada4175b164d364dc2d3f187bc8d93d32071a5ff588.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8c90f8de7ca9733bc9cad98cd0428374f8865999479a6a4391e8acef76aa1c23.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 6 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2]

-- Cycle fingerprint 8d943376c501e8202618685000ebafc3bc5b23b3f9fffabec7f9d5b49b535c4e.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint 8dd9428d2afef6c7eb50916c96517c41195ec22d6198c711455ae8a302f7187d.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 8e1213fc729e3841814247cc8207e12e96b3718848d764c0670749c08a201fe6.
def localCycle00117 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 15 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 8eaf0d614ae10483c41e7c0c0ee0655d85098684dca28e7be6f8720be5154ded.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 5, .triangle 3 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint 942ef8dc7a04139ef84e0284909905a2ecdc20037aca38b9d60d9beca27a3a87.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 949e4638b6d2d831c0c560024517b4997c50b34888c20b158374c08e2771ac27.
def localCycle00120 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 95aab7aaac90a027c7593e7361c507b6076a4f5ee21d93915778da5db18afca5.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -2, -2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 21 2, .gapLower 1 5, .gapLower 1 4, .triangle 22 1, .triangle 19 1]

-- Cycle fingerprint 9748cee83f9f3b974f4a0da8f0ac028b24a6c00a353a7e5701c1cb2803f71915.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 98e78291cf07a199cf9fb90a424839026fdaa41a88451621723794ee8136e549.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, true] }
  origin := ![.gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 99807877b99b25ec00848f123c8a836574679ad9b24362ab4d9ce87669df5d4f.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 99dc52f425147544b86cb5c5dfdcec6c997616b26ab64c4111a2ec1f87bb5ec0.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9be3e30a46291403b35ef33dcd7f97171e6e3cae798d55d26eb6534894f2b582.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9d2eca660af4dafc9b3f972883a07d605c1b28906c0a77802462b8550beb177c.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 9d83f6cef402aa7750061e5a3be6c467c8861ad9a23e8ace1f5676100b2db72a.
def localCycle00128 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint a0b1e0831d67f51fae8d034faf70d27f1dc427c97151f1522e757a0ea2d2f882.
def localCycle00129 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 19 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint a4e83a4f4c211c395544e557bf0c56eeef26f3f5a3fa7d0cc91e758ad3310d26.
def localCycle00130 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint a5c6efd22d28af51a7e79815eb4a01cd6e1f641223cd55b3dcb1901bccb097d8.
def localCycle00131 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5]
    constant := ![-1, 0, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 33 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2]

-- Cycle fingerprint a859fafa55636dfe346815b228be8d763cc87227513cb52049f1197c17645382.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, -1, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint a90d85cd5c9870a9d82653fd101820c3fd578229a3ff58838aa71eb53c7cb831.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6]
    constant := ![0, -2, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2]

-- Cycle fingerprint aa4b0ca9dae1f88d782ac18db92165972fb01e20d2c91ffbfb2653085cee8028.
def localCycle00134 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint acf0c128fc5ebab167868cbec0e55e4a912eccbdde51bd9fe045275ad5d3da4f.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .gapLower 3 0]

-- Cycle fingerprint adedc6d8fc48517d191d5d3fcb54829099a860ccc1fbd5d71388fe749718b65c.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint aea394be546750fc51638bbf37ce9fcc459ff26303e9a69302ea96594679fa8a.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4]
    constant := ![-3, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0]

-- Cycle fingerprint af907fd1376d48316549048429f9df9db6698ac39f4c6cb5bbbb5369bc317ec6.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint b25d24a4e807a52ac325632b4b249684b3a8ab6fdf71d3d7c59de11b7c77574c.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-1, -3, 0, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .gapLower 6 2, .triangle 4 0]

-- Cycle fingerprint b64c15880f9a2916e26496f34f0810a948c53d9c9c9e6e88501d465e98e477c6.
def localCycle00140 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint b8180b8176bc149e18d66149c06dd895e17ee9856ae8cb2b710448685113ec64.
def localCycle00141 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b86996485835149922fe0b5996aca0ce77f2ca107ec646116d55466fdeb80722.
def localCycle00142 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, -1, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint bd2f2b019b4b6bbb9b409f27bfd46dd9f5ea1259166197bc33a2b069d513816b.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bf054a62e6bd7e7de0f7ec57a9d5e805896cd6fd42453d1dbaf7c2748938afb2.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .triangle 22 1, .triangle 19 1]

-- Cycle fingerprint c0f39e2ea1dd6d824861d0217bae00782877f5f364fe64b0d58cb4d584e516b7.
def localCycle00145 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 5 0, .triangle 6 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint c1237a96e5f6f0c266e9f338059433e0be8541ad2605a67ec79df653dcd7cb5f.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c33a1ebfc62c4d5efc830d798c2f4e67e605fb014ec742590776b0e137053a74.
def localCycle00147 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c43f1eab1ac9ad8f17be759ea93358f79cc7e2da24091600889bc00284500c9b.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, -2, 0, -2, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint c4e31dcb4fffd0aa8cc63136a109ae01c6cb65739d78fd6a92a214a85021155e.
def localCycle00149 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 16 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c4f5619494b4db5cd4fc093f85e93af08cea8000b02cc217128610a841ed52f7.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint c71a7bd70f3c33466e0e0246ed9e62e9094fef51ed455022b1f1560b1145544e.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint c8493ca2639fd68c5c0b993d13fc85931f7fd36a1257caf16fe71442d721f8d9.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint cb2ce48e15f3a56ee4dce6e408187093b6c0100559c363a143d49fe49e8dcb71.
def localCycle00153 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 1 1, .triangle 15 1, .triangle 16 0, .corridorLower 2 4, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint cb7d96d8d542ea330942e95261ee34b4b81e48cf34f4cb00aee51615bb4ed7e7.
def localCycle00154 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 20 0, .gapLower 3 0]

-- Cycle fingerprint cd2556a937892e3e887a2766a6e06f88ae951ae080b2f57706e8c55ed0b46cd2.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint cdcab5d443c450a57855d19850ce42c4e61aa809f76233ae567cd48efbb267ed.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint cfce18e77336d4d3ed5557cfb172cb7efba350c83934700f0e9ad7cfa06d845b.
def localCycle00157 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint d0c7a021e0781e246fab119915fa121c343664ad6691d8513b326b12753cdc15.
def localCycle00158 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 2, .triangle 22 0, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint d21662db461cb51b3bee1156c11403cbc23061fe822d0f50cc7c6177311e182b.
def localCycle00159 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint d229a312444e413f42fedb97cacf880958057859889889d3e25371d93d09368f.
def localCycle00160 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![-1, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, true, true, true, false, false, false, false] }
  origin := ![.triangle 31 0, .triangle 32 0, .triangle 34 1, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint d266ab4ce02b242cdc7270fa8dda14e9f9e83fe32e7af87d0496f91417b919f1.
def localCycle00161 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d48b45a92016dc868a66032c00dd1774cf6c95327c2dabfa56fcfe93acbdc357.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, true, false, false] }
  origin := ![.triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint d4e4aec0a1e9b84b8fb24391979e5ea657e565ca2260401680342936a0229de3.
def localCycle00163 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .theta 5]
    constant := ![3, -1, 0, 0, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 0, .triangle 1 0, .triangle 15 1, .triangle 17 0, .triangle 26 1, .gapLower 5 0]

-- Cycle fingerprint d70fd614ec335e990f03d7e42a9e707ea59bbc9357f8245d351595d3b2932d47.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .triangle 4 0, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d8f3d092d33459aa9429b714293030d4bbe5fe60b598f40e1a52c6a7ff9bb6a6.
def localCycle00165 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![0, 0, -1, -1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 34 2, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint d9ebc4ac1ccb945dd9809172e769b49ef337930b73ae2760b96d10ca8dc21cf8.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint da13e768ceab42bfa1d198c98edaf33334f16ef7cd84c62d2a2f7b21cb70c46e.
def localCycle00167 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .gapLower 6 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint da353e1fffee6bc824426299eb2afa28bbb6dfcd85a319ffbc0a448b8b687c37.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 1 5, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5]

-- Cycle fingerprint db1921c166c1574e4125c254e96aebd5f853114a6cdf785c1192683794e67c41.
def localCycle00169 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6]
    constant := ![-1, -3, 0, 0, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 4 0, .gapLower 1 4, .triangle 20 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2]

-- Cycle fingerprint dd06d1970cc276e7b35ca9c22c306b32275aca9d81fcac66787b828bc6a839e5.
def localCycle00170 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint dd8a285ed5d8d8b50f6a3541a03cac5756dfe60eb5191c5e28497cf39396eeae.
def localCycle00171 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5]
    constant := ![-1, 0, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 30 0, .triangle 33 2, .triangle 21 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2]

-- Cycle fingerprint ddb6c0f069038d2d8e3d66f965530e80e5611e45f9a315e165a46b4b81b1deee.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero, .theta 6, .distance 0 6]
    constant := ![0, -1, -1, 0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 11 1, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint de1f896b559eb1aa0132c6100c7eda9baba87e63357f70c8b58da5357c06fec4.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint df172e0b3308457956e89c3d937857537aaae7b30a4750cc2cf7ec1f0240e02f.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint e081cdf6142a9bdfed4ad70eaff4c3f476bc20e5709646bee36ec14aec28a4a6.
def localCycle00175 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![-2, 0, -2, -1, 0, 0, 3, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2, .triangle 4 0, .triangle 3 0]

-- Cycle fingerprint e0836af74598004c92db6a66a642e9281d8007d1e370f931a932938b937ed8d4.
def localCycle00176 : Cycle where
  length := 14
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6]
    constant := ![0, -1, -1, 0, 0, 0, -1, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 6 2, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1]

-- Cycle fingerprint e1fb784ca7d0a90e5dce114907cf74684133b04404930c1c0ae05d6f0202b443.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .theta 5, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 6]
    constant := ![-2, -1, 0, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 3 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 34 0, .triangle 30 2, .triangle 18 2]

-- Cycle fingerprint e2df2f95d041bb065a394eba00892050dad91a1b4f5460ffa73882b3fa117933.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e5f68ce2133bf873ecee2c5ffaa8a3f4f2a906670460103bc07a1640c635fd5d.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint e8d8175d561f3a457336501f85a5f84cdd6b5c021ceae91e6496656c8804edc3.
def localCycle00180 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .gapUpper 5 0, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint e9a4887015205c002514f901e5723e992cbbab3db66a5fabc7f76c05d751e51e.
def localCycle00181 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e9f2470ba1292d9cf5385b39c32efaa74eaf0889fcfc13dccba956187c017078.
def localCycle00182 : Cycle where
  length := 14
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 0 1, .distance 0 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6]
    constant := ![0, -1, 0, 0, -1, -1, 0, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 6 2, .triangle 4 0, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint ebfe1b23fdd41b11213465c866775bdef438118f6ad4073917cf0c8b66fe992e.
def localCycle00183 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 22 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .gapLower 6 2, .triangle 4 0]

-- Cycle fingerprint ec684fd95099221ae7617853db4bf02c3b19cfcc00ca6b92de854edfb9cdcf51.
def localCycle00184 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint ec70f745c7f49dc5664aff98d1ad575f304fd55f9aedc66f2b8753257d21f64d.
def localCycle00185 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 22 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint ec7fcae8884b138b17af85940fafa162d299f4ac7929496d3855d808e44142eb.
def localCycle00186 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6]
    constant := ![-1, -1, -2, 0, -2, 0, 0, 3, 0, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, false, true, false] }
  origin := ![.triangle 4 0, .triangle 3 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2]

-- Cycle fingerprint ecad25e237ac5c4f259145acf4f34722d2b7f68604f3a48120012cd892a57a1f.
def localCycle00187 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, true] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint ecb72381678b45b51105becdc4c6344ab92550ae3ed6084b85c611d129be8e61.
def localCycle00188 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint ed51f1478def11fa1101a2187c343ec091ad56e5ccdae95d0f7152fb5f0ef5e1.
def localCycle00189 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint ee13c5ed7bbb69f8a90b740195d509204e7f26d33ef478c1ef07b5d0538f6870.
def localCycle00190 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 1 5, .triangle 3 0, .gapLower 5 0, .corridorUpper 4 5]

-- Cycle fingerprint efa0a82fece018917ff8756be9c5d782fb665cc0ab96753b96daed8b1f472d53.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 28 1, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4]

-- Cycle fingerprint f03b61f80f979553329ace9161adeb2fb68e67090e7b91103d2cc95f540554ca.
def localCycle00192 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f16da5612a7b132ce67c50f6d193169b39d4f5cc303679c03d42ebd5269d324f.
def localCycle00193 : Cycle where
  length := 13
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6]
    constant := ![0, -1, -2, -2, 0, 0, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 6 2, .triangle 4 0, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint f186166cbe386d35f6891ca2253626d39d4c6b1485ae9a3f96b479908834949f.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 3 0, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f1b1e88221ad00ca778f6a8a660cfab10d5ddbb0fd5541643c72717fac8ca18d.
def localCycle00195 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint f212fc7baef4cc4dd6ea98dc4faa63b64903546f115a3a048e21b6c2afc15be1.
def localCycle00196 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint f3a9343c537221fc7246cc8012e3f8ded3f6abf55e3dce31796b06a6475acc47.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint f7a1d47c26f1bd0c25e0cf06a2d91af8226b9db2dbf458ce1862775ab69881f0.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 1 5, .triangle 3 0, .triangle 22 1, .gapLower 4 0]

-- Cycle fingerprint f958595af3a7f96ea34fb6cf0844daeac7f178b9f5f096e1e8694819b3233bba.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint fa5a26f4eee76c6559264d3518ceb923afd72faf3e338e565751fb173da91d20.
def localCycle00200 : Cycle where
  length := 14
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![-2, -2, 0, 0, -1, 0, 0, 3, 0, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .gapLower 6 2, .triangle 4 0]

-- Cycle fingerprint fabd642eba3eb7662157cb6523fb6d61c844ef0fd1902479b5e791b06c132c74.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .zero, .theta 6, .distance 0 6, .distance 0 1]
    constant := ![-1, 0, -1, 0, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, true] }
  origin := ![.triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2, .thetaUpper 6, .gapUpper 6 0, .triangle 4 1]

-- Cycle fingerprint fb80d02c889b22f8a3870d5abac79f88489b49ea06f6c9c6caf72b739e9ddd2f.
def localCycle00202 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 7 0, .triangle 26 1, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint fd13419f5d72c7fbc06eafe8d205f1d8869ed4c4d11daddc77856786852d9540.
def localCycle00203 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 0 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 2, .triangle 4 0, .triangle 1 2, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint ffb0bc1131a8e299a81322fb3a9e70ec02de9cd04791bbb1d8c9a12769b9a880.
def localCycle00204 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, 0, -1, -1, -1, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

def library : Library := fun id => if id < 102 then (if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 76 then (if id < 63 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))))) else (if id < 69 then (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))))) else (if id < 89 then (if id < 82 then (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 85 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))))) else (if id < 95 then (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))))))) else (if id < 153 then (if id < 127 then (if id < 114 then (if id < 108 then (if id < 105 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)))) else (if id < 111 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))))) else (if id < 120 then (if id < 117 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))))) else (if id < 140 then (if id < 133 then (if id < 130 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)))) else (if id < 136 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))) else (if id < 146 then (if id < 143 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)))) else (if id < 149 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))))))) else (if id < 179 then (if id < 166 then (if id < 159 then (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)))) else (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))))) else (if id < 172 then (if id < 169 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))) else (if id < 175 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))) else (if id < 177 then (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)))))) else (if id < 192 then (if id < 185 then (if id < 182 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)))) else (if id < 188 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none))) else (if id < 190 then (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none)) else (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none))))) else (if id < 198 then (if id < 195 then (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))) else (if id < 201 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none))) else (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 5, 4, 3, 1, 6], ![2, 5, 4, 3, 0, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 71 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17024)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 5, 4, 3, 1, 6], ![2, 5, 4, 3, 0, 6], ![1, 0, 5, 4, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 26 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17025)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .low (![97, 144, 81, 101, 69, 8, 36, 104, 43, 180, 196, 112, 132, 72, 70, 107, 190, 122, 19, 100, 190, 159, 193, 190, 120, 168, 0, 197]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17026)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 160 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17027)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![1, 0, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 167 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17028)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .low (![97, 144, 81, 101, 69, 8, 36, 104, 43, 180, 196, 112, 132, 72, 70, 107, 190, 122, 19, 100, 190, 159, 193, 190, 120, 168, 0, 197]) }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17029)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 4, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 182 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17030)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 4, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 129 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17031)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 3, 4, 6], ![1, 5, 0, 2, 4, 6], ![1, 5, 0, 2, 3, 6], ![1, 4, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17032)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 3, 4, 6], ![1, 5, 0, 2, 6, 4], ![1, 5, 0, 2, 6, 3], ![1, 4, 3, 2, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 15 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17033)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 2, 6], ![1, 5, 0, 3, 2, 6], ![1, 4, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17034)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 4, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 184 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17035)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 4, 3, 6], ![1, 5, 4, 0, 2, 6], ![1, 5, 3, 0, 2, 6], ![1, 4, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 178 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17036)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 5, 0, 4, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 5, 0, 2, 6], ![1, 3, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 191 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17037)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 0, 3, 4, 6], ![1, 5, 0, 2, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17038)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 0, 3, 4, 6], ![1, 5, 0, 2, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 20 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17039)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17040)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 0, 4, 3, 6], ![1, 5, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17041)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 5, 0, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17042)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 0, 3, 4, 6], ![5, 1, 0, 2, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17043)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 0, 3, 4, 6], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 15 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17044)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 0, 4, 3, 6], ![5, 1, 0, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 179 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17045)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 0, 4, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 78 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17046)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 5, 4, 3, 0, 6], ![1, 5, 0, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 185 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17047)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![2, 5, 4, 3, 0, 6], ![1, 5, 0, 4, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 178 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17048)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![5, 2, 3, 4, 0, 6], ![5, 1, 0, 3, 4, 6], ![5, 1, 0, 2, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 73 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17049)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![5, 2, 3, 4, 0, 6], ![5, 1, 0, 3, 4, 6], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 174 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17050)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![5, 2, 3, 4, 0, 6], ![5, 1, 0, 4, 3, 6], ![5, 1, 0, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 187 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17051)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![5, 2, 3, 4, 0, 6], ![5, 1, 0, 4, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 78 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17052)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![5, 2, 4, 3, 0, 6], ![5, 1, 0, 4, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17053)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 2, 4, 3, 1, 6], ![5, 2, 4, 3, 0, 6], ![5, 1, 0, 4, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17054)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .low (![60, 144, 81, 101, 110, 98, 36, 104, 43, 180, 147, 4, 132, 72, 70, 164, 198, 194, 19, 75, 198, 141, 66, 118, 120, 108, 0, 197]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17055)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .low (![143, 146, 28, 139, 39, 114, 36, 189, 155, 180, 131, 103, 132, 130, 70, 63, 133, 194, 165, 199, 133, 141, 24, 85, 120, 30, 0, 197]) }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17056)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .low (![161, 80, 55, 101, 110, 98, 36, 116, 76, 180, 147, 4, 151, 119, 70, 164, 198, 194, 19, 128, 198, 141, 66, 118, 120, 108, 0, 197]) }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17057)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17058)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 106 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17059)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17060)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 5, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 3, 0, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 109 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17061)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 5, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 23 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17062)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 3, 5, 6, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 188 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17063)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 5, 3, 6, 4], ![1, 0, 5, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 3, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 23 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17064)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 5, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 5, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 3, 0, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 23 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17065)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 5, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 0, 5, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 1, 0, 2, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 91 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17066)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 157 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17067)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![1, 0, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 183 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17068)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![1, 0, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .low (![56, 142, 150, 166, 123, 170, 36, 47, 105, 186, 83, 37, 132, 74, 175, 40, 95, 194, 32, 204, 95, 141, 200, 87, 120, 162, 0, 197]) }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17069)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![1, 0, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 25 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17070)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 0, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 50 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17071)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 3, 6, 5, 4], ![1, 0, 2, 6, 5, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 0, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 79 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17072)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![1, 5, 0, 6, 2, 3], ![1, 4, 3, 2, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 15 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17073)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 0, 3, 6, 4], ![1, 5, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 3, 2, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 23 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17074)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 0, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 1, 2, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 91 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17075)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![5, 2, 3, 4, 0, 6], ![5, 1, 0, 3, 6, 4], ![5, 1, 0, 2, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 117 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17076)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 2, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 48 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17077)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 2, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 127 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17078)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 3, 5, 6], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 93 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17079)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 34 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17080)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 2, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17081)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 2, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 64 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17082)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17083)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 94 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17084)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 5, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 84 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17085)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 5, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 7 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17086)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 4, 5, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 124 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17087)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 4, 0, 3, 6], ![1, 4, 5, 0, 2, 6], ![1, 3, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 181 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17088)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 4, 0, 3, 6], ![1, 5, 4, 0, 2, 6], ![1, 5, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 29 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17089)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 4, 0, 3, 6], ![1, 5, 4, 0, 2, 6], ![5, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 158 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17090)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 4, 0, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17091)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![5, 2, 3, 4, 0, 6], ![5, 1, 4, 0, 3, 6], ![5, 1, 4, 0, 2, 6], ![5, 1, 3, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 173 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17092)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 2, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 99 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17093)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 2, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17094)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17095)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 4, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17096)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 2, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 127 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17097)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 46 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17098)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 2, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 136 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17099)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 94 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17100)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 4, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 94 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17101)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 34 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17102)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17103)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 202 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17104)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 4, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 124 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17105)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 4, 3, 5, 0, 6], ![1, 5, 4, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 1, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17106)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 4, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 149 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17107)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 4, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 7 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17108)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 4, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 2, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 124 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17109)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 4, 5, 3, 0, 6], ![1, 5, 4, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 1, 5, 2, 0, 6], ![3, 1, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17110)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 5, 4, 3, 0, 6], ![1, 5, 4, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 1, 2, 0, 6], ![3, 4, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 115 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17111)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![2, 5, 4, 3, 0, 6], ![1, 5, 4, 0, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 140 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17112)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![5, 2, 4, 3, 0, 6], ![5, 1, 4, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 1, 2, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 135 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17113)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![5, 2, 4, 3, 0, 6], ![5, 1, 4, 0, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 1, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 173 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17114)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 2, 1, 0, 5, 6], ![1, 0, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 86 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17115)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 2, 1, 0, 5, 6], ![1, 0, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 153 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17116)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![1, 3, 0, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 172 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17117)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![4, 2, 5, 3, 0, 6], ![4, 1, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![3, 1, 0, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 201 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17118)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 2, 1, 0, 6, 5], ![1, 0, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 42 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17119)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 145 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17120)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 2, 1, 0, 6, 5], ![1, 0, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 13 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17121)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 5, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![1, 3, 0, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 203 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17122)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 2, 5, 3, 1, 6], ![4, 2, 5, 3, 0, 6], ![4, 1, 0, 5, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![3, 1, 0, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 65 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17123)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 2, 3, 5, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 22 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17124)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 11 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17125)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 192 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17126)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![4, 2, 3, 5, 0, 6], ![4, 1, 5, 0, 3, 6], ![4, 1, 5, 0, 2, 6], ![3, 2, 1, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 134 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17127)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![4, 2, 5, 3, 0, 6], ![4, 1, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 11 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17128)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![4, 2, 5, 3, 0, 6], ![4, 1, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 192 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17129)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![4, 2, 5, 3, 0, 6], ![4, 1, 5, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 134 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17130)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![4, 5, 2, 3, 0, 6], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 59 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17131)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 5, 2, 3, 1, 6], ![4, 5, 2, 3, 0, 6], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 163 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17132)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![4, 5, 2, 3, 0, 6], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17133)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![5, 4, 2, 3, 0, 6], ![4, 5, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17134)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![5, 4, 2, 3, 0, 6], ![5, 4, 1, 0, 3, 6], ![4, 5, 1, 0, 2, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17135)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![5, 4, 2, 3, 1, 6], ![5, 4, 2, 3, 0, 6], ![5, 4, 1, 0, 3, 6], ![5, 4, 1, 0, 2, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17136)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .low (![97, 144, 81, 101, 14, 52, 36, 104, 43, 180, 3, 82, 132, 72, 70, 68, 9, 194, 19, 148, 16, 141, 138, 18, 120, 121, 0, 197]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17137)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .low (![97, 144, 81, 101, 49, 52, 36, 104, 43, 180, 88, 82, 132, 72, 70, 68, 177, 194, 19, 148, 177, 141, 138, 177, 120, 10, 0, 197]) }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17138)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 152 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17139)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 2, 6], ![1, 0, 4, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .low (![33, 41, 137, 101, 14, 52, 36, 67, 111, 180, 3, 82, 132, 6, 70, 68, 9, 194, 19, 148, 16, 141, 138, 18, 120, 121, 0, 197]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17140)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 45 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17141)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 3, 5, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 17 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17142)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 5, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 5, 4, 6, 3], ![1, 5, 0, 4, 6, 2], ![1, 5, 0, 3, 2, 6], ![1, 4, 3, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17143)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 5, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 0, 5, 4, 6, 3], ![1, 5, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 1, 3, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17144)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 5, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 0, 5, 4, 6, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 113 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17145)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 176 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17146)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .low (![125, 53, 81, 54, 169, 77, 36, 156, 43, 180, 171, 96, 151, 72, 70, 58, 62, 194, 51, 31, 57, 141, 89, 1, 120, 35, 0, 197]) }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17147)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 3, 4, 5, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 61 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17148)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 4, 5, 0, 6], ![1, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 2], ![1, 5, 0, 3, 2, 6], ![1, 4, 3, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17149)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 3, 5, 4, 0, 6], ![1, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 1, 3, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17150)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![5, 2, 3, 4, 1, 6], ![2, 5, 3, 4, 0, 6], ![1, 5, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 113 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 17151)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (17024 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 17024 ≤ id.val) (hhigh : id.val < 17152) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 17024)) = true := by
  let j : Fin 128 := ⟨id.val - 17024, by omega⟩
  have hsum : 17024 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (17024 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard133
