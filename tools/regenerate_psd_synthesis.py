#!/usr/bin/env python3
"""Regenerate D1 exact candidates. No solver, reconstructed floats or target repair."""
from pathlib import Path
import synthesize_psd_factors as synth
import import_exact_gram_bundle as gram

ROOT = Path(__file__).resolve().parents[1]


def generate() -> dict[Path, str]:
    suite = gram.load_json(ROOT / 'data/fixtures/psd_synthesis/cases.json')
    gram.check_keys(suite, '$', required=('format', 'cases'))
    if suite['format'] != 'leanpep-psd-regression-cases-v1':
        raise ValueError('unexpected regression fixture format')
    blocks = ['import LeanPEP.GramPEP.FactorReplacement\n']
    reports = []
    names: set[str] = set()
    for case in suite['cases']:
        gram.check_keys(case, '$.cases[]', required=('name','origin','pivot_order','input'))
        name = gram.require_string(case['name'], '$.cases[].name')
        if '.' in name or name in names:
            raise ValueError('case names must be unique single Lean identifiers')
        names.add(name)
        ns = 'LeanPEP.Imported.PSDSynthesized.' + name
        gram.validate_namespace(ns)
        matrix = synth.parse_matrix_input(case['input'])
        result = synth.synthesize_psd(matrix, pivot_order=case['pivot_order'])
        report = synth.result_report(matrix, result)
        report.update(case=name, origin=case['origin'])
        reports.append(report)
        blocks.append(synth.render_matrix_lean(matrix,result,ns).split('\n',1)[1])
    raw = gram.load_json(ROOT / 'data/fixtures/gram_external/one_step_exact.json')
    rebuilt, report = synth.refactor_bundle(raw)
    if rebuilt is None:
        raise ArithmeticError('GD exact regression matrices unexpectedly failed')
    return {
        ROOT/'LeanPEP/Imported/PSDSynthesized.lean':'\n'.join(blocks),
        ROOT/'data/fixtures/psd_synthesis_generated/cases_report.json':synth.dumps(reports),
        ROOT/'data/fixtures/psd_synthesis_generated/gd_one_step_refactored.json':synth.dumps(rebuilt),
        ROOT/'data/fixtures/psd_synthesis_generated/gd_one_step_report.json':synth.dumps(report),
        ROOT/'LeanPEP/Imported/GramOneStepResynthesized.lean':
            synth.render_bundle_data(rebuilt,'LeanPEP.Imported.GramOneStepResynthesized'),
    }


def main() -> None:
    for path, text in generate().items():
        gram.atomic_write(path,text)
        print(path.relative_to(ROOT))


if __name__ == '__main__':
    main()
