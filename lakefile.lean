import Lake
open Lake DSL

package «lean4-smrd» where
  name := "lean4-smrd"

@[default_target]
lean_lib «SMRD» where
  globs := #[.andSubmodules `SMRD]
