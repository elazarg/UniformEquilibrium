/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.Basic
import MathUE.DirectedTransport.Additive.CirculationDecomposition
import MathUE.DirectedTransport.Additive.Circuits
import MathUE.DirectedTransport.Additive.Cycles
import MathUE.DirectedTransport.Additive.Quantitative
import MathUE.DirectedTransport.Additive.ShortCycles
import MathUE.DirectedTransport.CategoricalRetractAdapter
import MathUE.DirectedTransport.CategoricalRetracts
import MathUE.DirectedTransport.Category
import MathUE.DirectedTransport.Closure
import MathUE.DirectedTransport.Exact
import MathUE.DirectedTransport.FiniteInequality.Arithmetic
import MathUE.DirectedTransport.FiniteInequality.Quantitative
import MathUE.DirectedTransport.FiniteInequality.Sparse
import MathUE.DirectedTransport.JoinSemidirect
import MathUE.DirectedTransport.JoinSemidirectMaxAffine
import MathUE.DirectedTransport.MaxAffine.Arithmetic
import MathUE.DirectedTransport.MaxAffine.Basic
import MathUE.DirectedTransport.MaxAffine.CycleSlack
import MathUE.DirectedTransport.MaxAffine.Duality
import MathUE.DirectedTransport.MaxAffine.GaugeFeasibility
import MathUE.DirectedTransport.MaxAffine.GaugeHolonomy
import MathUE.DirectedTransport.MaxAffine.Paths
import MathUE.DirectedTransport.MaxAffine.Relaxation
import MathUE.DirectedTransport.MaxAffine.Slopes
import MathUE.DirectedTransport.MaxAffine.Sparse
import MathUE.DirectedTransport.NormalForms
import MathUE.DirectedTransport.PotentialRigidity
import MathUE.DirectedTransport.SCC

/-!
# Directed transport theory

This umbrella exposes the project-owned generic theory of exact and lax
directed transport: categorical and strongly connected normal forms,
complete-lattice closure, additive cycle and circulation duality, finite
inequality certificates, join-semidirect labels, and max-affine transport.

The computational core remains in `MathUE.DirectedTransport`.  The modules
above extend that core without game-semantic assumptions.
-/
