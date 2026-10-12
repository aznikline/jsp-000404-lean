import Mathlib
import Jsp000404.S7N7Defs
import Jsp000404.S8Defs

/-!
# Compatibility shell for the scalar seven/eight-centre definitions

The old `Jsp000404.S7Defs` had both the `N7` and the `N8` scalar models. They now live in
`Jsp000404.S7N7Defs` (`N7`, frozen AIR bytes) and `Jsp000404.S8Defs` (`N8`). Importing this
module gives the same declarations, plus the umbrella `Mathlib` import the old file had.
-/
