"""Read and validate the project's explicit result selection."""
import json
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def fraction(value):
    if isinstance(value, dict):
        return Q(int(value['numerator']), int(value['denominator']))
    return Q(value)


def load():
    registry = json.loads((ROOT / 'results/registry.json').read_text())
    if registry['schema'] != 1:
        raise ValueError('unknown result registry schema')
    entries = registry['results']
    ids = [r['id'] for r in entries]
    if len(ids) != len(set(ids)) or registry['current'] not in ids:
        raise ValueError('duplicate IDs or missing current result')
    for result in entries:
        if result['status'] not in ('candidate', 'proposed', 'historical-proposed'):
            raise ValueError('unknown result status')
        if not (ROOT / result['record']).is_file():
            raise ValueError('missing result record')
        records = result.get('paper_records', [result['record']])
        if result['record'] not in records or len(records) != len(set(records)):
            raise ValueError('invalid paper record list')
        if any(not (ROOT / path).is_file() for path in records):
            raise ValueError('missing inherited paper record')
        if result['status'] == 'candidate':
            continue
        for key in ('certificate', 'verifier'):
            if not (ROOT / result[key]).is_file():
                raise ValueError(f'missing {key} for {result["id"]}')
        delta = Q(result['fourier_saving'])
        if not 0 < delta < 1:
            raise ValueError('invalid Fourier saving')
        if result['tensor_saving'] is not None:
            a = Q(result['tensor_saving'])
            if not delta < a < 1:
                raise ValueError('no positive absorption gap')
            c = json.loads((ROOT / result['certificate']).read_text())
            values = c.get('certificate', c)
            reported_delta = values.get('fourier_saving', values.get('fourier_delta'))
            if fraction(values['tensor_saving']) != a or fraction(reported_delta) != delta:
                raise ValueError('registry parameters differ from certificate')
            if 'source_manifest' in result:
                source = json.loads((ROOT / result['source_manifest']).read_text())
                key = result.get('certificate_source', Path(result['source_manifest']).parent.name)
                pin = c['source']['commit'] if 'source' in c else c['sources'][key]['commit']
                if source['commit'] != pin:
                    raise ValueError('source commit differs from certificate')
    current = next(r for r in entries if r['id'] == registry['current'])
    if current['status'] != 'proposed':
        raise ValueError('current result must have an incorporated proposed transfer')
    return registry, current


def exact_decimal(value):
    from decimal import Decimal, localcontext
    q = Q(value)
    with localcontext() as ctx:
        ctx.prec = 30
        return format(Decimal(q.numerator) / Decimal(q.denominator), 'f').rstrip('0').rstrip('.')
