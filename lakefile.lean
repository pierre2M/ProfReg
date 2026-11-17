import Lake
open Lake DSL

package «ProfReg» where
  -- options du package

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "1a59aa5b8603fd850ee2dc6ef9e35a44fe351599"  -- [D-14, 27/09/2026] épinglé sur la révision du manifeste (était "master")

@[default_target]
lean_lib «ProfReg» where