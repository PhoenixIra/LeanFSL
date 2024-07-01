import Lake
open Lake DSL

package «InvLimDiss» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.9.0"

@[default_target]
lean_lib «InvLimDiss» where
  -- add any library configuration options here
