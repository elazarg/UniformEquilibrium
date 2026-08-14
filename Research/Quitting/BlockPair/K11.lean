import Research.Quitting.BlockPair.K11.Preconditioner
import Research.Quitting.BlockPair.K11.ConditionalPackage
import Research.Quitting.BlockPair.K11.JacobianCache
import Research.Quitting.BlockPair.K11.KrawczykConditionalConsumer
import Research.Quitting.BlockPair.K11.KrawczykConditionalData
import Research.Quitting.BlockPair.K11.KrawczykConditionalSemantic
import Research.Quitting.BlockPair.K11.RowZeroCacheData
import Research.Quitting.BlockPair.K11.RowZeroSemantic
import UniformEquilibrium.Quitting.Examples.BlockPair.K11ActiveEquationInterval

/-!
# Period-eleven BlockPair research interfaces

This umbrella contains the trust-clean compositional conditional compiler,
conditional consumers, and semantic adapters that can be maintained
independently of the numeric certificate payloads.  Active-equation semantics
come from their canonical production owner.  The quarantined payloads remain
listed in `K11/MANIFEST.md` but are not imported.
-/
