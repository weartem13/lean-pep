"""Maintenance coverage and printed-axiom gates; these tests do not run Lean."""
import json
from pathlib import Path
import unittest
from unittest import mock

from scripts import verify


class VerificationEntryTests(unittest.TestCase):
    def checklist(self):
        return json.loads((verify.ROOT / 'scripts/verification.json').read_text())

    def test_all_library_and_original_smoke_coverage(self):
        coverage = verify.validate_checklist(verify.ROOT, self.checklist())
        self.assertEqual(coverage['library_modules'], 247)
        self.assertEqual(coverage['aggregate_project_modules'], 238)  # includes LeanPEP.lean
        self.assertEqual(coverage['unaggregated_modules'], 10)
        self.assertEqual(coverage['smoke_files'], 73)
        self.assertEqual(coverage['regression_files'], 4)

    def test_old_critical_replays_are_retained(self):
        required = {
            'tests/lean/regression/pg_one_tightness.lean',
            'tests/lean/regression/pg_one_regression.lean',
            'tests/lean/regression/gd_one_tightness.lean',
            'tests/lean/regression/gd_one_regression.lean',
            'data/cases/pg/two-step-original/Replay.lean',
            'data/cases/pg/three-step-original/Replay.lean',
            'data/cases/gd/one-step-upper/Replay.lean',
            'data/cases/gd/two-step-original/Replay.lean',
            'data/cases/gd/one-step-gap/PrimalReplay.lean',
        }
        checklist = self.checklist()
        self.assertLessEqual(required, set(checklist['regression_files'] + checklist['replay_files']))

    def test_missing_smoke_or_module_fails_before_execution(self):
        for key in ('smoke_files', 'unaggregated_modules', 'replay_files'):
            checklist = self.checklist()
            checklist[key].pop(0)
            with self.subTest(key=key), self.assertRaises(ValueError):
                verify.validate_checklist(verify.ROOT, checklist)

    def test_full_plan_executes_every_listed_lean_file_once(self):
        checklist = self.checklist()
        plan = verify.plan('full', Path('/private/tmp/unexecuted-verification-plan'), 'python3')
        direct = [entry['argv'][3] for entry in plan if entry['argv'][:3] == ['lake', 'env', 'lean']]
        expected = checklist['smoke_files'] + checklist['regression_files'] + checklist['replay_files'] + [checklist['interface_file']]
        self.assertCountEqual(direct, expected)
        self.assertEqual(len(direct), len(set(direct)))
        self.assertTrue(any(entry['label'] == 'pg2_recover' for entry in plan))
        self.assertTrue(any(entry['label'] == 'cleanup_dry_run' for entry in plan))

    def test_standard_and_no_axiom_outputs_are_accepted(self):
        text = "'N.a' depends on axioms: [propext, Classical.choice, Quot.sound]\n'N.b' does not depend on any axioms\n"
        result = verify.axiom_audit(text, ['a', 'N.b'])
        self.assertTrue(result['passed'])
        self.assertEqual(result['printed_declarations'], 2)

    def test_nonstandard_missing_malformed_or_sorry_output_rejected(self):
        for text, expected in [
            ("'N.a' depends on axioms: [customAxiom]", ['a']),
            ("'N.a' depends on axioms: [sorryAx]", ['a']),
            ("'N.a' depends on axioms: [propext]", ['a', 'b']),
            ("'N.a' depends on axioms: [propext", []),
            ("N.a does not depend on any axioms", []),
            ("warning: declaration uses 'sorry'", []),
        ]:
            with self.subTest(text=text):
                self.assertFalse(verify.axiom_audit(text, expected)['passed'])

    def test_direct_lean_audit_requires_each_source_print(self):
        source = verify.ROOT / 'examples/interface.lean'
        names = ['LeanPEP.ActualFunction.ProximalGradientSparseAudit.upper_analytic',
                 'LeanPEP.ActualFunction.ProximalGradientCaptureAudit.upper_analytic']
        text = '\n'.join("'" + name + "' depends on axioms: [propext]" for name in names)
        argv = ['lake', 'env', 'lean', str(source)]
        self.assertTrue(verify.command_axiom_audit(verify.ROOT, argv, text)['passed'])
        self.assertFalse(verify.command_axiom_audit(verify.ROOT, argv, text.splitlines()[0])['passed'])

    def test_source_output_refused_without_spawning(self):
        with mock.patch('sys.argv', ['verify.py', 'quick', '--output', str(verify.ROOT)]), \
                mock.patch.object(verify.subprocess, 'Popen') as spawn:
            with self.assertRaises(SystemExit) as raised:
                verify.main()
            self.assertEqual(raised.exception.code, 2)
            spawn.assert_not_called()


if __name__ == '__main__':
    unittest.main()
