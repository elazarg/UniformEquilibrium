from pathlib import Path

path = Path('UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/StoppingLaw/SelfOrientedAtomSequence.lean')
text = path.read_text(encoding='utf-8')
text = text.replace(
    '    apply FinDist.expect_mono\n',
    '    apply Math.Probability.FinDist.expect_mono\n',
    1,
)
text = text.replace(
    '    simpa only [charge] using\n      (continuous_quittingTerminalSemanticDebt owner).tendsto frontier.base |>.comp\n        hprofilesSubseq\n',
    '    simpa only [charge, Function.comp_apply] using\n      (continuous_quittingTerminalSemanticDebt owner).tendsto frontier.base |>.comp\n        hprofilesSubseq\n',
    1,
)
text = text.replace(
    '    linarith [hsourceDebt n, hgain, herrorLe]\n',
    '    unfold quittingPureTimeUpdatedProfile\n    linarith [hsourceDebt n, hgain, herrorLe]\n',
    1,
)
path.write_text(text, encoding='utf-8')
