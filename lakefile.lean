import Lake
open Lake DSL

package «lean_evm» {
  -- add package configuration options here
  srcDir := "src"
}

lean_lib «LeanEVM» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean_evm» {
  root := `Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v2024"
require auto from git "https://github.com/leanprover-community/lean-auto"@"v0.0.5"
