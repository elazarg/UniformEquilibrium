import Research.Quitting.BlockPair.K11.Preconditioner
import Research.Quitting.BlockPair.K11.ActiveEquationSemanticAdapter
import Research.Quitting.BlockPair.K11.ConditionalStrategicCompiler
import Research.Quitting.BlockPair.K11.ConditionalPackage
import Research.Quitting.BlockPair.K11.JacobianCache
import Research.Quitting.BlockPair.K11.KrawczykConditionalConsumer
import Research.Quitting.BlockPair.K11.KrawczykConditionalData
import Research.Quitting.BlockPair.K11.KrawczykConditionalSemantic
import Research.Quitting.BlockPair.K11.RowZeroCacheData
import Research.Quitting.BlockPair.K11.RowZeroSemantic

/-!
# Period-eleven BlockPair research interfaces

This umbrella contains the trust-clean conditional consumers and semantic
adapters that can be maintained independently of the numeric certificate
payloads.  The latter remain listed in `K11/Manifest.md` but are not imported.
-/
