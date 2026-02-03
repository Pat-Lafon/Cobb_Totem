import Lake
open Lake DSL

package «Cobb_Totem» where
  -- You can add package metadata here if needed

require aesop from git "https://github.com/leanprover-community/aesop.git" @ "v4.28.0-rc1"
require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "v4.27.0"

@[default_target]
lean_lib «Cobb_Totem» where
  roots := #[`Main]
