import Lake
open Lake DSL

package «CodeBench» where
  -- add package configuration options here

lean_lib «CodeBench» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «codebench» where
  root := `Main
