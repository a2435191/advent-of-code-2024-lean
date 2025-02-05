import Lake
open Lake DSL

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "mathlib" @ git "master"

package «advent-of-code-2024» where
  -- add package configuration options here

lean_lib «AdventOfCode2024» where
  -- add library configuration options here

@[default_target]
lean_exe «advent-of-code-2024» where
  root := `Main
