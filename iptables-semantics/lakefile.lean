import Lake
open Lake DSL

package «iptables-semantics»

require aesop from git
  "https://github.com/leanprover-community/aesop" @ "v4.26.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "v4.26.0"

@[default_target]
lean_lib «IptablesSemantics» where
  globs := #[.submodules `IptablesSemantics]
