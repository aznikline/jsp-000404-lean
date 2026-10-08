import Jsp000404.SevenLowerBranchLibraries

/-! SOURCE_ONLY fixed-context certificate proof candidate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Jsp404.SevenLowerFixedCutContexts
open SevenLowerReplay
def context000 : Context :=
  emptyContext

def context001 : Context :=
  setTriangle (emptyContext) 0 false

def context002 : Context :=
  setTriangle (setTriangle (emptyContext) 0 false) 1 false

def context003 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false

def context004 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false

def context005 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false

def context006 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false

def context007 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false

def context008 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false

def context009 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false

def context010 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false

def context011 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 0

def context012 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 1

def context013 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 2

def context014 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 3

def context015 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 4

def context016 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5

def context017 : Context :=
  setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false

def context018 : Context :=
  setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false

def context019 : Context :=
  setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false) 12 false

def context020 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false) 12 false) 13 false

def context021 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false) 12 false) 13 true

def context022 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false) 12 false) 13 true) 15 false

def context023 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false) 12 false) 13 true) 15 true

def context024 : Context :=
  setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 false) 12 true

def context025 : Context :=
  setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 false) 11 true

def context026 : Context :=
  setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true

def context027 : Context :=
  setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true) 13 false

def context028 : Context :=
  setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true) 13 false) 14 false

def context029 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true) 13 false) 14 false) 11 false

def context030 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true) 13 false) 14 false) 11 true

def context031 : Context :=
  setTriangle (setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true) 13 false) 14 true

def context032 : Context :=
  setTriangle (setTriangle (setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 5) 10 true) 13 true

def context033 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 6

def context034 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 7

def context035 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 8

def context036 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 9

def context037 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 10

def context038 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 11

def context039 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 12

def context040 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 13

def context041 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 14

def context042 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 15

def context043 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 16

def context044 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 17

def context045 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 18

def context046 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 19

def context047 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 false) 20

def context048 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 false) 9 true

def context049 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 false) 8 true

def context050 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true

def context051 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 false

def context052 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 false) 8 false

def context053 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 false) 8 true

def context054 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true

def context055 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 0

def context056 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 1

def context057 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 2

def context058 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 3

def context059 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 4

def context060 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 5

def context061 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 6

def context062 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 7

def context063 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 8

def context064 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 9

def context065 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 10

def context066 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 11

def context067 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 12

def context068 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 13

def context069 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 14

def context070 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 15

def context071 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 16

def context072 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 17

def context073 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 18

def context074 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 19

def context075 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 false) 7 true) 9 true) 20

def context076 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 true

def context077 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 true) 7 false

def context078 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 false) 6 true) 7 true

def context079 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true

def context080 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true) 9 false

def context081 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true) 9 false) 6 false

def context082 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true) 9 false) 6 false) 8 false

def context083 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true) 9 false) 6 false) 8 true

def context084 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true) 9 false) 6 true

def context085 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 false) 5 true) 9 true

def context086 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true

def context087 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false

def context088 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false

def context089 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 false

def context090 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 false) 6 false

def context091 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 false) 6 false) 9 false

def context092 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 false) 6 false) 9 true

def context093 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 false) 6 true

def context094 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true

def context095 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false

def context096 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 false

def context097 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true

def context098 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 0

def context099 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 1

def context100 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 2

def context101 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 3

def context102 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 4

def context103 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 5

def context104 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 6

def context105 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 7

def context106 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 8

def context107 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 9

def context108 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 10

def context109 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 11

def context110 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 12

def context111 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 13

def context112 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 14

def context113 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 15

def context114 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 16

def context115 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 17

def context116 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 18

def context117 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 19

def context118 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true) 20

def context119 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 false) 5 true) 9 true

def context120 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 true

def context121 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 true) 5 false

def context122 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 false) 8 true) 5 true

def context123 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true

def context124 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 false

def context125 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 false) 8 false

def context126 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 false) 8 false) 6 false

def context127 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 false) 8 false) 6 true

def context128 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 false) 8 true

def context129 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true

def context130 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 0

def context131 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 1

def context132 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 2

def context133 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 3

def context134 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 4

def context135 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 5

def context136 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 6

def context137 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 7

def context138 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 8

def context139 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 9

def context140 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 10

def context141 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 11

def context142 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 12

def context143 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 13

def context144 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 14

def context145 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 15

def context146 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 16

def context147 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 17

def context148 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 18

def context149 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 19

def context150 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 false) 4 true) 7 true) 9 true) 20

def context151 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true

def context152 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 false

def context153 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 false) 5 false

def context154 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 false) 5 false) 7 false

def context155 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 false) 5 false) 7 true

def context156 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 false) 5 true

def context157 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true

def context158 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 false

def context159 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 false) 5 false

def context160 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 false) 5 true

def context161 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true

def context162 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 0

def context163 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 1

def context164 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 2

def context165 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 3

def context166 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 4

def context167 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 5

def context168 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 6

def context169 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 7

def context170 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 8

def context171 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 9

def context172 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 10

def context173 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 11

def context174 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 12

def context175 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 13

def context176 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 14

def context177 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 15

def context178 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 16

def context179 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 17

def context180 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 18

def context181 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 19

def context182 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 false) 3 true) 4 true) 7 true) 20

def context183 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true

def context184 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false

def context185 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false

def context186 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 false

def context187 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 false) 6 false

def context188 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 false) 6 false) 8 false

def context189 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 false) 6 false) 8 true

def context190 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 false) 6 true

def context191 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 true

def context192 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 true) 8 false

def context193 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 true) 8 false) 6 false

def context194 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 true) 8 false) 6 true

def context195 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 false) 4 true) 8 true

def context196 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true

def context197 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 false

def context198 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true

def context199 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 0

def context200 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 1

def context201 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 2

def context202 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 3

def context203 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 4

def context204 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 5

def context205 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 6

def context206 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 7

def context207 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 8

def context208 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 9

def context209 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 10

def context210 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 11

def context211 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 12

def context212 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 13

def context213 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 14

def context214 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 15

def context215 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 16

def context216 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 17

def context217 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 18

def context218 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 19

def context219 : Context :=
  setHeavy (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 false) 3 true) 4 true) 20

def context220 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 true

def context221 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 true) 4 false

def context222 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 false) 2 true) 9 true) 4 true

def context223 : Context :=
  setTriangle (setTriangle (emptyContext) 0 false) 1 true

def context224 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false

def context225 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false

def context226 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false

def context227 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false

def context228 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 false

def context229 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 false) 6 false

def context230 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 false) 6 false) 9 false

def context231 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 false) 6 false) 9 true

def context232 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 false) 6 true

def context233 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 true

def context234 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 true) 9 false

def context235 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 true) 9 false) 6 false

def context236 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 true) 9 false) 6 true

def context237 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 false) 5 true) 9 true

def context238 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 true

def context239 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 true) 5 false

def context240 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 false) 3 true) 5 true

def context241 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true

def context242 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true) 9 false

def context243 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true) 9 false) 3 false

def context244 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true) 9 false) 3 false) 6 false

def context245 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true) 9 false) 3 false) 6 true

def context246 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true) 9 false) 3 true

def context247 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 false) 2 true) 9 true

def context248 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 true

def context249 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 true) 2 false

def context250 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 true) 2 false) 5 false

def context251 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 true) 2 false) 5 true

def context252 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 false) 8 true) 2 true

def context253 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true

def context254 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false

def context255 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false) 8 false

def context256 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false) 8 false) 3 false

def context257 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false) 8 false) 3 false) 6 false

def context258 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false) 8 false) 3 false) 6 true

def context259 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false) 8 false) 3 true

def context260 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 false) 8 true

def context261 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 false) 1 true) 7 true) 9 true

def context262 : Context :=
  setTriangle (emptyContext) 0 true

def context263 : Context :=
  setTriangle (setTriangle (emptyContext) 0 true) 4 false

def context264 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false

def context265 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false

def context266 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false

def context267 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false

def context268 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false

def context269 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 false

def context270 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 false) 8 false

def context271 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 false) 8 false) 9 false

def context272 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 false) 8 false) 9 true

def context273 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 false) 8 true

def context274 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 true

def context275 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 true) 9 false

def context276 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 true) 9 false) 8 false

def context277 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 true) 9 false) 8 true

def context278 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 false) 7 true) 9 true

def context279 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 true

def context280 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 true) 7 false

def context281 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 false) 3 true) 7 true

def context282 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true

def context283 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true) 9 false

def context284 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true) 9 false) 3 false

def context285 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true) 9 false) 3 false) 8 false

def context286 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true) 9 false) 3 false) 8 true

def context287 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true) 9 false) 3 true

def context288 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 false) 2 true) 9 true

def context289 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true

def context290 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false

def context291 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false

def context292 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 false

def context293 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 false) 3 false

def context294 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 false) 3 false) 9 false

def context295 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 false) 3 false) 9 true

def context296 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 false) 3 true

def context297 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 true

def context298 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 true) 9 false

def context299 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 true) 9 false) 3 false

def context300 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 true) 9 false) 3 true

def context301 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 false) 2 true) 9 true

def context302 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 true

def context303 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 true) 2 false

def context304 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 false) 8 true) 2 true

def context305 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true

def context306 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true) 9 false

def context307 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true) 9 false) 8 false

def context308 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true) 9 false) 8 false) 3 false

def context309 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true) 9 false) 8 false) 3 true

def context310 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true) 9 false) 8 true

def context311 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 false) 1 true) 7 true) 9 true

def context312 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true

def context313 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 false

def context314 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 false) 2 false

def context315 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 false) 2 false) 7 false

def context316 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 false) 2 false) 7 true

def context317 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 false) 2 true

def context318 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 true

def context319 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 true) 7 false

def context320 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 true) 7 false) 2 false

def context321 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 true) 7 false) 2 true

def context322 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 false) 6 true) 1 true) 7 true

def context323 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true

def context324 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false

def context325 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false

def context326 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 false

def context327 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 false) 3 false

def context328 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 false) 3 false) 8 false

def context329 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 false) 3 false) 8 true

def context330 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 false) 3 true

def context331 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 true

def context332 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 true) 8 false

def context333 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 true) 8 false) 3 false

def context334 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 true) 8 false) 3 true

def context335 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 false) 1 true) 8 true

def context336 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 true

def context337 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 true) 1 false

def context338 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 false) 6 true) 1 true

def context339 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 true

def context340 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 true) 1 false

def context341 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 false) 5 true) 9 true) 1 true

def context342 : Context :=
  setTriangle (setTriangle (emptyContext) 0 true) 4 true

def context343 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false

def context344 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false

def context345 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false

def context346 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false

def context347 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 false

def context348 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 false) 3 false

def context349 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 false) 3 false) 9 false

def context350 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 false) 3 false) 9 true

def context351 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 false) 3 true

def context352 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 true

def context353 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 true) 9 false

def context354 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 true) 9 false) 3 false

def context355 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 true) 9 false) 3 true

def context356 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 false) 2 true) 9 true

def context357 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 true

def context358 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 true) 2 false

def context359 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 false) 6 true) 2 true

def context360 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true

def context361 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true) 9 false

def context362 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true) 9 false) 6 false

def context363 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true) 9 false) 6 false) 3 false

def context364 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true) 9 false) 6 false) 3 true

def context365 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true) 9 false) 6 true

def context366 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 false) 5 true) 9 true

def context367 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 true

def context368 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 true) 5 false

def context369 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 true) 5 false) 2 false

def context370 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 true) 5 false) 2 true

def context371 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 false) 8 true) 5 true

def context372 : Context :=
  setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true

def context373 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false

def context374 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false) 8 false

def context375 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false) 8 false) 6 false

def context376 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false) 8 false) 6 false) 3 false

def context377 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false) 8 false) 6 false) 3 true

def context378 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false) 8 false) 6 true

def context379 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 false) 8 true

def context380 : Context :=
  setTriangle (setTriangle (setTriangle (setTriangle (emptyContext) 0 true) 4 true) 7 true) 9 true

end Jsp404.SevenLowerFixedCutContexts
