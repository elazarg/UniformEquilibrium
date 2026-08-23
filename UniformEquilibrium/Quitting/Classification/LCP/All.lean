/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Classification.LCP.Normalization
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalRestriction
import UniformEquilibrium.Quitting.Classification.LCP.PrincipalReward
import UniformEquilibrium.Quitting.Classification.LCP.NormalPrincipalQBar
import UniformEquilibrium.Quitting.Classification.LCP.NormalPrincipalReward
import UniformEquilibrium.Quitting.Classification.LCP.ReturnedBlockTangentGap
import UniformEquilibrium.Quitting.Classification.LCP.ProjectiveQBarBehavioralDecoder
import UniformEquilibrium.Quitting.Classification.LCP.StrategicTransport
import UniformEquilibrium.Quitting.Classification.LCP.MatrixClasses
import UniformEquilibrium.Quitting.Classification.LCP.StationaryEquilibrium
import UniformEquilibrium.Quitting.Classification.LCP.NormalCore
import UniformEquilibrium.Quitting.Classification.LCP.NormalCoreStrictnessExample
import UniformEquilibrium.Quitting.Classification.LCP.CyclicParametricQ
import UniformEquilibrium.Quitting.Classification.LCP.StandardQSideExample
import UniformEquilibrium.Quitting.Classification.LCP.ThreeByThreeZeroDiagonalQ
import UniformEquilibrium.Quitting.Classification.LCP.Gate
import UniformEquilibrium.Quitting.Classification.LCP.FirstLayerSimple
import UniformEquilibrium.Quitting.Classification.LCP.LaterLayerAbnormal
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer
import UniformEquilibrium.Quitting.Classification.LCP.IsolatedEndpointProducer
import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQProducer
import UniformEquilibrium.Quitting.Classification.LCP.SupportHierarchy
import UniformEquilibrium.Quitting.Classification.LCP.OrdinaryNonQClosure
import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary
import UniformEquilibrium.Quitting.Classification.LCP.StationaryExistence
import UniformEquilibrium.Quitting.Classification.LCP.ZeroSoloGeneratedStandardQ
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.All
import UniformEquilibrium.Quitting.Classification.LCP.FullCore.All

/-!
# LCP normalization and algebraic classification for finite quitting games

This umbrella exports the theorem-bearing infrastructure proved in this folder:

* the faithful playerwise solo normalization with explicit nontermination
  payoff;
* exact strategic transport of ordinary terminal approximate-Nash inequalities;
* the standard/projective Q split and projective Q-bar;
* the audit of the earlier draft's normal-player recursion together with the
  source's distinct-witness object and an explicit quitting table on which its
  stabilized core is strictly smaller than the one-step screen;
* exact four-player quitting tables witnessing satisfiability of the
  normal-core standard-Q, nonhomogeneous necessary condition, including
  a witness whose normal core is the full four-player set;
* the exact nonhomogeneous standard-Q region `0 < a < b` for the
  two-parameter cyclic singleton-comparison family;
* the complete zero-diagonal `3 × 3` classification: outside the homogeneous
  branch, standard Q is exactly one of the two strict directed-cycle sign
  orientations together with positive determinant;
* the elimination of every quitting game whose normal core has
  exactly three players, so every four-player counterexample has full core;
* the exact carrier fixed point and `1/14` global-debt upper bound for every
  completion of the displayed four-player full-core deadlock matrix;
* the unconditional algebraic matrix-regime gate with its precise residual
  class; and
* the complete all-abnormal producer, including the later-layer
  two-scale owner/blocker construction;
* the complete homogeneous producer, including both vertex and
  nonvertex simplex witnesses; and
* the complete ordinary non-Q producer, including the all-Continue
  provenance contradiction, the contracting multi-hazard endpoint, and the
  isolated-endpoint blocker repair; and
* the sharp unconditional counterexample restriction: the normal
  core is nonempty, nonhomogeneous, and its principal matrix is textbook
  standard Q (hence also projective Q); and
* the stationary strengthening of that restriction: all three producers off
  the standard-Q side deliver a payoff vector approached by *stationary*
  `ε`-equilibria, which is the source's Section 5 conclusion shape.

It deliberately does not export a source-theorem record or a completed
strategic classification theorem.  Concrete sunspot semantics, continuous
absorption paths, and the
absorption-path-to-ordinary compiler remain explicit obligations.
-/
