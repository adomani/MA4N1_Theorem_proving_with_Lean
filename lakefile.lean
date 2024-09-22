import Lake
open Lake DSL

package «mA4N1» where
  leanOptions := #[
    ⟨`weak.lang.lemmaCmd, true⟩
  ]
  -- add any package configuration options here
  moreServerOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`weak.lang.lemmaCmd, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MA4N1» {
  -- add any library configuration options here
  roots := #[`MA4N1]
}
