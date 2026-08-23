import Literature.Catalog

/-!
# Literature audit

Bibliography label: Jointly Controlled Lotteries with Biased Coins

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.JointlyControlledLotteriesWithBiasedCoins

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "jointly_controlled_lotteries_with_biased_coins"
  bibliographyLabel := "Jointly Controlled Lotteries with Biased Coins"
  bibliographyLocator :=
    "Published source: " ++
      "Jointly Controlled Lotteries with Biased Coins"
  role := .recentNonzeroSum
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.JointlyControlledLotteriesWithBiasedCoins
