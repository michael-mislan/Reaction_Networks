"""Validate accepted papers against the fixed scope of this migration."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED_IDS = [f'P{i:03d}' for i in range(1, 83)]

def validate(manifest, rows):
    if manifest.get('expected_ids') != EXPECTED_IDS:
        raise ValueError('Expected inventory must retain P001 through P082 in order')
    entries = manifest.get('papers', [])
    ids = [entry['id'] for entry in entries]
    if len(ids) != len(set(ids)) or set(ids) != set(EXPECTED_IDS):
        raise ValueError('Expected inventory has missing or duplicate paper IDs')
    allowed = {'ACCEPTED', 'PENDING_SOURCE_REVIEW'}
    if any(entry.get('status') not in allowed for entry in entries):
        raise ValueError('Unknown expected-paper acceptance status')
    accepted = {entry['id'] for entry in entries if entry['status'] == 'ACCEPTED'}
    row_ids = [row['id'] for row in rows]
    if len(row_ids) != len(set(row_ids)) or set(row_ids) != accepted:
        raise ValueError('Accepted dossier inventory differs from expected-paper states')
    for row in rows:
        if (row.get('mapping_status') != 'VERIFIED' or
            row.get('copy_status') != 'COPIED' or row.get('hash_status') != 'PASS' or
            row.get('dependency_status') != 'COMPLETE'):
            raise ValueError('Accepted paper has incomplete migration gates: ' + row['id'])
    return [entry for entry in entries if entry['status'] != 'ACCEPTED']

def inventory(rows):
    manifest = json.loads((ROOT/'migration/expected-papers.json').read_text(encoding='utf8'))
    pending = validate(manifest, rows)
    return len(EXPECTED_IDS), pending
