import Experiments.certsearch.block_pair.K11.DyadicData
import Experiments.certsearch.block_pair.K11.JacobianCache
import Experiments.certsearch.block_pair.K11.Preconditioner
import Experiments.certsearch.block_pair.K11.RowZeroCacheData
import Experiments.certsearch.block_pair.K11.KrawczykConditionalConsumer

namespace GameTheory.BlockPairK11.DyadicCertificate

/-- Assembly of the checked K11 numeric payloads into the reusable
`K11KrawczykData` checker interface. This declaration records the current
exact data flow. -/
def checkedK11KrawczykData : K11KrawczykData where
  precision := Precision
  center := center
  radius := radius
  radius_nonneg := by norm_num [radius]
  box := box
  preconditioner := preconditioner
  jacobianBoxCache := fun row column ↦
    (jacobianBoxCache.get row).get column
  residualAtCenterCache := fun row ↦ residualAtCenterCache.get row

end GameTheory.BlockPairK11.DyadicCertificate
