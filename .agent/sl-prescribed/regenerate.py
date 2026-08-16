from pathlib import Path
import json
import re

root = Path('.')
ledger_path = root / 'docs/QuittingProofFrontier.json'
ledger = json.loads(ledger_path.read_text(encoding='utf-8'))
ledger['open_leaf_limit'] = 3

resolution = 'ELIMINATE-PRESCRIBED-BY-SELF-ORIENTED-PURE-TIME'
for alternative in ledger['manuscript_alternatives']:
    if alternative['issue_number'] == 3:
        alternative.pop('leaf_id', None)
        alternative['status'] = 'eliminated'
        alternative['resolution'] = resolution

ledger['formal_leaves'] = [
    leaf for leaf in ledger['formal_leaves']
    if leaf['id'] != 'SL-PRESCRIBED'
]
source = (
    'UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/'
    'StoppingLaw/ThreeWayLocalization.lean'
)
representatives = {
    'SL-ABSENT-WALL': (
        'packet.owner.1 ∉ packet.terminal.val ∧ '
        'HasQuittingPureTimeObserverAbsentForcedOwnerDispatch '
        '(quittingStoppingLawSelfOrientedBaseProfile packet) '
        'packet.owner.1 '
        '(quittingStoppingLawSelfOrientedCarrierQuitTime packet) '
        'packet.terminal '
        '(quittingStoppingLawSelfOrientedMassLower packet)'
    ),
    'SL-NEG-TARGET': (
        'packet.owner.1 ∈ packet.terminal.val ∧ '
        'reward packet.terminal packet.owner.1 < 0 ∧ '
        'HasQuittingPureTimeNegativeTargetAtomicDispatch '
        '(quittingStoppingLawSelfOrientedBaseProfile packet) '
        'packet.owner.1 packet.sourceQuitTime packet.terminal '
        '(quittingStoppingLawSelfOrientedMassLower packet)'
    ),
    'SL-POS-TARGET': (
        'packet.owner.1 ∈ packet.terminal.val ∧ '
        '0 < reward packet.terminal packet.owner.1 ∧ '
        'HasQuittingPureTimePositiveTargetReachedRowLocalization '
        'frontier '
        '(quittingStoppingLawSelfOrientedBaseProfile packet) '
        'packet.owner.1 packet.targetQuitTime packet.terminal '
        '(quittingStoppingLawSelfOrientedMassLower packet)'
    ),
}
for leaf in ledger['formal_leaves']:
    leaf['source'] = source
    leaf['producer'] = (
        'QuittingCounterexampleStoppingLawFrontier.threeWayLocalization'
    )
    leaf['representative'] = representatives[leaf['id']]

old_path = (
    'UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/'
    'StoppingLaw/FourWayLocalization.lean'
)
transitions = []
for transition in ledger['transitions']:
    transition['target_ids'] = [
        target for target in transition.get('target_ids', [])
        if target != 'SL-PRESCRIBED'
    ]
    transition['evidence'] = [
        source if evidence == old_path else evidence
        for evidence in transition.get('evidence', [])
    ]
    if transition['id'] == 'PRESERVE-RECTANGLE-ORIENTATION-PROVENANCE':
        transition['id'] = 'PRESERVE-SELF-ORIENTED-PURE-TIME-PROVENANCE'
        transition['summary'] = (
            'The exhaustive capstone retains one self-oriented pure-time '
            'atom packet, its fixed terminal label, and the owner-membership '
            'and reward-sign facts selecting one of the three remaining '
            'consumers.'
        )
        transition['evidence'] = [source]
    elif transition['id'] == 'FRONTIER-BASELINE':
        transition['summary'] = (
            'Mechanically exhaustive antichain: three formal leaves in two '
            'obstruction classes, together with an exact bundled three-way '
            'localization of every counterexample regime.'
        )
        transition['evidence'] = [source]
    if transition['target_ids']:
        transitions.append(transition)

transitions.insert(0, {
    'id': resolution,
    'kind': 'leaf_eliminated',
    'target_ids': ['SL-ABSENT-WALL', 'SL-NEG-TARGET', 'SL-POS-TARGET'],
    'summary': (
        'Choose one positive-debt owner and purify both a near-worst source '
        'and a near-best target to deterministic Quit times. Own-strategy '
        'updates preserve the owner cap, so a fixed terminal atom carries a '
        'positive target-minus-source gain while target debt vanishes. Owner '
        'incidence and reward sign route that atom into the three remaining '
        'consumers; manuscript Alternative 1 and issue #3 need no separate '
        'prescribed-comparison branch.'
    ),
    'evidence': [
        'UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/'
        'StoppingLaw/SelfOrientedAtomSequence.lean',
        'UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/'
        'StoppingLaw/PureTimeDispatch.lean',
        source,
    ],
})
ledger['transitions'] = transitions
ledger_path.write_text(
    json.dumps(ledger, indent=2, ensure_ascii=False) + '\n',
    encoding='utf-8',
)

status_path = root / 'docs/ProjectStatus.json'
status = json.loads(status_path.read_text(encoding='utf-8'))
status['quitting_frontier']['summary'] = (
    'The quitting proof search has three mechanically checkable open leaves. '
    'The general and all-quitting conjectures remain open independently of '
    'any one certificate grammar.'
)
status_path.write_text(
    json.dumps(status, indent=2, ensure_ascii=False) + '\n',
    encoding='utf-8',
)

toolkit_path = root / 'docs/TOOLKIT.md'
toolkit = toolkit_path.read_text(encoding='utf-8')
replacement = (
    '| Quitting counterexample localization | '
    '`UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegime/'
    'StoppingLaw/ThreeWayLocalization.lean` | Nonexistence produces one '
    'counterexample regime, an exhaustive stopping-law frontier, and a '
    'self-oriented pure-time atom routed into its three-way localization. '
    'The prescribed-payoff comparison is absent; no converse is claimed '
    'from the branch data. |'
)
toolkit, count = re.subn(
    r'^\| Quitting counterexample localization \|.*$',
    replacement,
    toolkit,
    count=1,
    flags=re.MULTILINE,
)
if count != 1:
    raise SystemExit('failed to update TOOLKIT localization row')
toolkit_path.write_text(toolkit, encoding='utf-8')

three_path = root / source
three = three_path.read_text(encoding='utf-8')
marker = '\nend GameTheory\n'
if 'exists_stoppingLaw_threeWayLocalization' not in three:
    addition = '''

/-- A counterexample regime supplies a three-way localization on one of its
stopping-law frontiers. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_threeWayLocalization
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      HasQuittingStoppingLawThreeWayLocalization frontier := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨frontier, frontier.threeWayLocalization⟩

/-- Failure of ordinary uniform-payoff existence produces a counterexample
regime, a frontier, and its three-way localization. -/
theorem exists_stoppingLaw_threeWayLocalization_of_not_exists_uniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ regime : QuittingCounterexampleRegime reward,
      ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
        HasQuittingStoppingLawThreeWayLocalization frontier := by
  let regime := quittingCounterexampleRegimeOfNoUniformPayoff reward hno
  obtain ⟨frontier, hlocalization⟩ :=
    regime.exists_stoppingLaw_threeWayLocalization
  exact ⟨regime, frontier, hlocalization⟩
'''
    if marker not in three:
        raise SystemExit('missing ThreeWayLocalization end marker')
    three = three.rsplit(marker, 1)[0] + addition + marker
    three_path.write_text(three, encoding='utf-8')

shim = root / old_path
shim.write_text('''/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.ThreeWayLocalization

/-!
# Compatibility import for the former four-way localization module

The canonical exhaustive result is now `threeWayLocalization`. This module
retains only the old import path for source links and downstream imports; it
defines no prescribed-comparison branch.
-/
''', encoding='utf-8')
