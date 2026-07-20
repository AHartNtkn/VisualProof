import manifest from '../../../content/manifest.json'
import progression from '../../../content/progression/core.json'
import catalog from '../../../content/catalog/cursebreaker.json'
import guidance from '../../../content/guidance/cursebreaker.json'
import onboardingTwoVeils from '../../../content/puzzles/two-veils.json'
import onboardingFourVeils from '../../../content/puzzles/four-veils.json'
import onboardingForkedVeil from '../../../content/puzzles/forked-veil.json'
import onboardingEchoedVeil from '../../../content/puzzles/echoed-veil.json'
import onboardingEmptyRingRelease from '../../../content/puzzles/empty-ring-release.json'
import puzzle0 from '../../../content/puzzles/single-mark-return.json'
import markedEchoDeiteration from '../../../content/puzzles/marked-echo-deiteration.json'
import puzzle1 from '../../../content/puzzles/shallow-edit-legality-contrast.json'
import puzzle2 from '../../../content/puzzles/atomic-fragment-erasure.json'
import puzzle3 from '../../../content/puzzles/atomic-content-insertion.json'
import puzzle4 from '../../../content/puzzles/compound-copy-authority-contrast.json'
import puzzle5 from '../../../content/puzzles/transfer-duplication-recognition.json'
import puzzle6 from '../../../content/puzzles/atomic-double-cut-selection.json'
import puzzle7 from '../../../content/puzzles/common-conjunction-factor-base.json'
import puzzle8 from '../../../content/puzzles/common-disjunction-factor-base.json'
import puzzle9 from '../../../content/puzzles/compound-common-disjunction-factor.json'
import puzzle10 from '../../../content/puzzles/compound-double-cut-selection.json'
import puzzle11 from '../../../content/puzzles/content-bearing-annulus-choice.json'
import puzzle12 from '../../../content/puzzles/disjunction-over-conjunction-base.json'
import puzzle13 from '../../../content/puzzles/i-dao.json'
import puzzle14 from '../../../content/puzzles/nested-owner-introduction.json'
import puzzle15 from '../../../content/puzzles/polarity-bubble-contrast.json'
import puzzle16 from '../../../content/puzzles/rm-fa.json'
import puzzle17 from '../../../content/puzzles/useful-vacuous-owner-workspace.json'
import puzzle18 from '../../../content/puzzles/conjunction-idempotence-introduction.json'
import puzzle20 from '../../../content/puzzles/compound-weakening-boundary.json'
import puzzle21 from '../../../content/puzzles/two-mark-projection.json'
import puzzle22 from '../../../content/puzzles/compound-projection.json'
import puzzle23 from '../../../content/puzzles/ternary-projection-choice.json'
import puzzle24 from '../../../content/puzzles/left-injection-introduction.json'
import puzzle25 from '../../../content/puzzles/grouped-branch-construction.json'
import puzzle26 from '../../../content/puzzles/injection-branch-contrast.json'
import puzzle27 from '../../../content/puzzles/compound-conjunction-idempotence.json'
import puzzle28 from '../../../content/puzzles/disjunction-idempotence-introduction.json'
import puzzle29 from '../../../content/puzzles/compound-disjunction-idempotence.json'
import puzzle30 from '../../../content/puzzles/atomic-conjunction-exchange.json'
import puzzle31 from '../../../content/puzzles/compound-conjunction-exchange.json'
import puzzle32 from '../../../content/puzzles/disjunction-exchange-recognition.json'
import puzzle33 from '../../../content/puzzles/compound-disjunction-exchange.json'
import puzzle34 from '../../../content/puzzles/conjunction-reassociation-recognition.json'
import puzzle35 from '../../../content/puzzles/conjunction-reassociation-role-scope.json'
import puzzle36 from '../../../content/puzzles/disjunction-reassociation-recognition.json'
import puzzle37 from '../../../content/puzzles/structural-recognition-routing-choice.json'
import puzzle38 from '../../../content/puzzles/disjunction-reassociation-role-scope.json'
import puzzle39 from '../../../content/puzzles/i-c3.json'
import puzzle40 from '../../../content/puzzles/i-c4.json'
import puzzle41 from '../../../content/puzzles/r1.json'
import puzzle42 from '../../../content/puzzles/i-cs.json'
import puzzle43 from '../../../content/puzzles/i-al.json'
import puzzle44 from '../../../content/puzzles/ch-and.json'
import puzzle45 from '../../../content/puzzles/i-case2.json'
import puzzle46 from '../../../content/puzzles/rm-case3.json'
import puzzle47 from '../../../content/puzzles/i-om.json'
import puzzle48 from '../../../content/puzzles/ch-or.json'
import puzzle49 from '../../../content/puzzles/ternary-branchwise-map.json'
import puzzle50 from '../../../content/puzzles/i-aa.json'
import puzzle51 from '../../../content/puzzles/b6.json'
import puzzle52 from '../../../content/puzzles/i-ao.json'
import puzzle53 from '../../../content/puzzles/rm-ao.json'
import puzzle54 from '../../../content/puzzles/sey-ctr-i01.json'
import puzzle55 from '../../../content/puzzles/sey-ctr-r01.json'
import puzzle56 from '../../../content/puzzles/atomic-excluded-middle.json'
import puzzle57 from '../../../content/puzzles/sey-lem-i01.json'
import puzzle58 from '../../../content/puzzles/sey-lem-c01.json'
import puzzle59 from '../../../content/puzzles/atomic-negated-disjunction-forward.json'
import puzzle60 from '../../../content/puzzles/atomic-negated-disjunction-reverse.json'
import puzzle61 from '../../../content/puzzles/sey-dm-ec-i01.json'
import puzzle62 from '../../../content/puzzles/sey-dm-ec-c01.json'
import puzzle63 from '../../../content/puzzles/sey-dm-ed-i01.json'
import puzzle64 from '../../../content/puzzles/sey-dm-fc-i01.json'
import puzzle65 from '../../../content/puzzles/compound-conjunction-de-morgan.json'
import puzzle67 from '../../../content/puzzles/sey-red-c01.json'
import puzzle68 from '../../../content/puzzles/sey-pei-i01.json'
import puzzle69 from '../../../content/puzzles/sey-pei-c01.json'
import puzzle70 from '../../../content/puzzles/compound-context-threaded-choice.json'
import puzzle71 from '../../../content/puzzles/assumption-relevant-structured-reductio.json'
import puzzle72 from '../../../content/puzzles/weakening-injection-weave.json'
import puzzle73 from '../../../content/puzzles/contrapositive-composition-bridge.json'
import puzzle74 from '../../../content/puzzles/excluded-middle-manufactures-cases.json'
import puzzle75 from '../../../content/puzzles/alternating-negation-cnf.json'
import puzzle76 from '../../../content/puzzles/alternating-negation-dnf.json'
import puzzle77 from '../../../content/puzzles/b3.json'
import puzzle78 from '../../../content/puzzles/branch-preparation-common-tail.json'
import puzzle79 from '../../../content/puzzles/branch-preparation-local-chains.json'
import puzzle80 from '../../../content/puzzles/classical-consensus-branch-building.json'
import puzzle81 from '../../../content/puzzles/classical-consensus-product-collapsing.json'
import puzzle82 from '../../../content/puzzles/de-morgan-product-consumer.json'
import puzzle83 from '../../../content/puzzles/de-morgan-sum-consumer.json'
import puzzle84 from '../../../content/puzzles/double-cut-copy-license.json'
import puzzle85 from '../../../content/puzzles/double-cut-insertion-workspace.json'
import puzzle86 from '../../../content/puzzles/preserve-sole-structural-source.json'
import puzzle87 from '../../../content/puzzles/r4.json'
import puzzle88 from '../../../content/puzzles/r5.json'
import puzzle89 from '../../../content/puzzles/recollect-shared-branch-context.json'
import puzzle90 from '../../../content/puzzles/rm-c3.json'
import puzzle91 from '../../../content/puzzles/sey-ref-sel-i01.json'
import puzzle92 from '../../../content/puzzles/compound-theorem-source-choice.json'
import puzzle93 from '../../../content/puzzles/useful-manifestation-target.json'
import puzzle94 from '../../../content/puzzles/sey-ref-dis-i01.json'
import puzzle95 from '../../../content/puzzles/compound-context-dissolution.json'
import puzzle96 from '../../../content/puzzles/artifact-creates-copy-authority.json'
import puzzle97 from '../../../content/puzzles/artifact-polarity-direction-contrast.json'
import puzzle98 from '../../../content/puzzles/artifact-preserves-copy-authority.json'
import puzzle99 from '../../../content/puzzles/artifact-selected-downstream-bridge.json'
import puzzle100 from '../../../content/puzzles/blank-witness.json'
import seyricFieldEditContrast from '../../../content/puzzles/seyric-field-edit-contrast.json'
import seyricCompoundCopyAuthority from '../../../content/puzzles/seyric-compound-copy-authority.json'
import seyricAtomicDoubleCutSelection from '../../../content/puzzles/seyric-atomic-double-cut-selection.json'
import seyricExtractionContinuation from '../../../content/puzzles/seyric-extraction-continuation.json'
import type { GameContentFiles } from '../content-loader'

export const gameContentFiles: GameContentFiles = Object.freeze({
  'manifest.json': manifest,
  'progression/core.json': progression,
  'catalog/cursebreaker.json': catalog,
  'guidance/cursebreaker.json': guidance,
  'puzzles/two-veils.json': onboardingTwoVeils,
  'puzzles/four-veils.json': onboardingFourVeils,
  'puzzles/forked-veil.json': onboardingForkedVeil,
  'puzzles/echoed-veil.json': onboardingEchoedVeil,
  'puzzles/empty-ring-release.json': onboardingEmptyRingRelease,
  'puzzles/single-mark-return.json': puzzle0,
  'puzzles/marked-echo-deiteration.json': markedEchoDeiteration,
  'puzzles/shallow-edit-legality-contrast.json': puzzle1,
  'puzzles/atomic-fragment-erasure.json': puzzle2,
  'puzzles/atomic-content-insertion.json': puzzle3,
  'puzzles/compound-copy-authority-contrast.json': puzzle4,
  'puzzles/transfer-duplication-recognition.json': puzzle5,
  'puzzles/atomic-double-cut-selection.json': puzzle6,
  'puzzles/common-conjunction-factor-base.json': puzzle7,
  'puzzles/common-disjunction-factor-base.json': puzzle8,
  'puzzles/compound-common-disjunction-factor.json': puzzle9,
  'puzzles/compound-double-cut-selection.json': puzzle10,
  'puzzles/content-bearing-annulus-choice.json': puzzle11,
  'puzzles/disjunction-over-conjunction-base.json': puzzle12,
  'puzzles/i-dao.json': puzzle13,
  'puzzles/nested-owner-introduction.json': puzzle14,
  'puzzles/polarity-bubble-contrast.json': puzzle15,
  'puzzles/rm-fa.json': puzzle16,
  'puzzles/useful-vacuous-owner-workspace.json': puzzle17,
  'puzzles/conjunction-idempotence-introduction.json': puzzle18,
  'puzzles/compound-weakening-boundary.json': puzzle20,
  'puzzles/two-mark-projection.json': puzzle21,
  'puzzles/compound-projection.json': puzzle22,
  'puzzles/ternary-projection-choice.json': puzzle23,
  'puzzles/left-injection-introduction.json': puzzle24,
  'puzzles/grouped-branch-construction.json': puzzle25,
  'puzzles/injection-branch-contrast.json': puzzle26,
  'puzzles/compound-conjunction-idempotence.json': puzzle27,
  'puzzles/disjunction-idempotence-introduction.json': puzzle28,
  'puzzles/compound-disjunction-idempotence.json': puzzle29,
  'puzzles/atomic-conjunction-exchange.json': puzzle30,
  'puzzles/compound-conjunction-exchange.json': puzzle31,
  'puzzles/disjunction-exchange-recognition.json': puzzle32,
  'puzzles/compound-disjunction-exchange.json': puzzle33,
  'puzzles/conjunction-reassociation-recognition.json': puzzle34,
  'puzzles/conjunction-reassociation-role-scope.json': puzzle35,
  'puzzles/disjunction-reassociation-recognition.json': puzzle36,
  'puzzles/structural-recognition-routing-choice.json': puzzle37,
  'puzzles/disjunction-reassociation-role-scope.json': puzzle38,
  'puzzles/i-c3.json': puzzle39,
  'puzzles/i-c4.json': puzzle40,
  'puzzles/r1.json': puzzle41,
  'puzzles/i-cs.json': puzzle42,
  'puzzles/i-al.json': puzzle43,
  'puzzles/ch-and.json': puzzle44,
  'puzzles/i-case2.json': puzzle45,
  'puzzles/rm-case3.json': puzzle46,
  'puzzles/i-om.json': puzzle47,
  'puzzles/ch-or.json': puzzle48,
  'puzzles/ternary-branchwise-map.json': puzzle49,
  'puzzles/i-aa.json': puzzle50,
  'puzzles/b6.json': puzzle51,
  'puzzles/i-ao.json': puzzle52,
  'puzzles/rm-ao.json': puzzle53,
  'puzzles/sey-ctr-i01.json': puzzle54,
  'puzzles/sey-ctr-r01.json': puzzle55,
  'puzzles/atomic-excluded-middle.json': puzzle56,
  'puzzles/sey-lem-i01.json': puzzle57,
  'puzzles/sey-lem-c01.json': puzzle58,
  'puzzles/atomic-negated-disjunction-forward.json': puzzle59,
  'puzzles/atomic-negated-disjunction-reverse.json': puzzle60,
  'puzzles/sey-dm-ec-i01.json': puzzle61,
  'puzzles/sey-dm-ec-c01.json': puzzle62,
  'puzzles/sey-dm-ed-i01.json': puzzle63,
  'puzzles/sey-dm-fc-i01.json': puzzle64,
  'puzzles/compound-conjunction-de-morgan.json': puzzle65,
  'puzzles/sey-red-c01.json': puzzle67,
  'puzzles/sey-pei-i01.json': puzzle68,
  'puzzles/sey-pei-c01.json': puzzle69,
  'puzzles/compound-context-threaded-choice.json': puzzle70,
  'puzzles/assumption-relevant-structured-reductio.json': puzzle71,
  'puzzles/weakening-injection-weave.json': puzzle72,
  'puzzles/contrapositive-composition-bridge.json': puzzle73,
  'puzzles/excluded-middle-manufactures-cases.json': puzzle74,
  'puzzles/alternating-negation-cnf.json': puzzle75,
  'puzzles/alternating-negation-dnf.json': puzzle76,
  'puzzles/b3.json': puzzle77,
  'puzzles/branch-preparation-common-tail.json': puzzle78,
  'puzzles/branch-preparation-local-chains.json': puzzle79,
  'puzzles/classical-consensus-branch-building.json': puzzle80,
  'puzzles/classical-consensus-product-collapsing.json': puzzle81,
  'puzzles/de-morgan-product-consumer.json': puzzle82,
  'puzzles/de-morgan-sum-consumer.json': puzzle83,
  'puzzles/double-cut-copy-license.json': puzzle84,
  'puzzles/double-cut-insertion-workspace.json': puzzle85,
  'puzzles/preserve-sole-structural-source.json': puzzle86,
  'puzzles/r4.json': puzzle87,
  'puzzles/r5.json': puzzle88,
  'puzzles/recollect-shared-branch-context.json': puzzle89,
  'puzzles/rm-c3.json': puzzle90,
  'puzzles/sey-ref-sel-i01.json': puzzle91,
  'puzzles/compound-theorem-source-choice.json': puzzle92,
  'puzzles/useful-manifestation-target.json': puzzle93,
  'puzzles/sey-ref-dis-i01.json': puzzle94,
  'puzzles/compound-context-dissolution.json': puzzle95,
  'puzzles/artifact-creates-copy-authority.json': puzzle96,
  'puzzles/artifact-polarity-direction-contrast.json': puzzle97,
  'puzzles/artifact-preserves-copy-authority.json': puzzle98,
  'puzzles/artifact-selected-downstream-bridge.json': puzzle99,
  'puzzles/blank-witness.json': puzzle100,
  'puzzles/seyric-field-edit-contrast.json': seyricFieldEditContrast,
  'puzzles/seyric-compound-copy-authority.json': seyricCompoundCopyAuthority,
  'puzzles/seyric-atomic-double-cut-selection.json': seyricAtomicDoubleCutSelection,
  'puzzles/seyric-extraction-continuation.json': seyricExtractionContinuation,
})
