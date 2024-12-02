import Lake
open Lake DSL

package «advent-of-code-2024» where
  -- add package configuration options here

lean_lib «AdventOfCode2024» where
  -- add library configuration options here

@[default_target]
lean_exe «advent-of-code-2024» where
  root := `Main
