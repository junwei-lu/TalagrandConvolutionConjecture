import Lake
open Lake DSL

package "TalagrandConvConjecture" where
  version := v!"0.1.0"
  keywords := #["math", "probability", "boolean-analysis"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩
  ]

-- Mathlib pinned to the same tag as StatLean so the two agree on one Mathlib
-- and the cluster's shared compiled-Mathlib cache (rev 5e932f97dd25) applies.
require "leanprover-community" / "mathlib" @ git "v4.29.1"

-- StatLean loaded from GitHub (release a13a30b6, 2026-08-17), NOT the local
-- checkout: this project is an independent Lake project with its own history.
require StatLean from git
  "https://github.com/StatLean/Stat-Lean.git" @ "a13a30b639a8a8a11e3f81e9f6dbb4a088d4300e"

@[default_target]
lean_lib «TalagrandConvConjecture» where
