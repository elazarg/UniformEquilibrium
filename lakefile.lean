import Lake

open Lake DSL

abbrev uniformEquilibriumLeanOptions : Array LeanOption := #[
  ⟨`pp.unicode.fun, true⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`warningAsError, true⟩
]

package UniformEquilibrium where
  version := v!"0.1.0"
  keywords := #["game-theory", "stochastic-games", "uniform-equilibrium"]
  fixedToolchain := true

require GameTheory from "GameTheory"

@[default_target]
lean_lib MathUE where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions

@[default_target]
lean_lib UniformEquilibrium where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions ++ #[
    ⟨`synthInstance.maxSize, .ofNat 1024⟩
  ]

@[default_target]
lean_lib Literature where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions

@[default_target]
lean_lib Research where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions

@[default_target]
lean_lib Theorems where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions

@[default_target]
lean_lib Experiments where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions

@[default_target]
lean_lib AxiomAudit where
  srcDir := "."
  leanOptions := uniformEquilibriumLeanOptions
