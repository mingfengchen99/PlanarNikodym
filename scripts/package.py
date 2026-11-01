#!/usr/bin/env python3
"""Package the verified project, excluding caches and temporary files."""
import argparse
import json
from pathlib import Path
import subprocess
import zipfile

from check_layout import ROOT, check_layout, sha256, source_digest, source_manifest

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT.parent/'PlanarNikodym-organized.zip')
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        raise ValueError('write the archive outside the source project')
    check_layout()
    summary = json.loads((ROOT/'verification'/'summary.json').read_text())
    manifest = json.loads((ROOT/'verification'/'source-manifest.json').read_text())
    if source_manifest() != manifest or source_digest(manifest) != summary['source_digest']:
        raise ValueError('sources changed after verification; run bash scripts/check.sh')
    log = (ROOT/'verification'/'check.log').read_bytes()
    if sha256(log) != summary['check_log_sha256']:
        raise ValueError('verification log does not match its summary')
    dependencies = json.loads((ROOT/'lake-manifest.json').read_text())
    for package in dependencies['packages']:
        path = ROOT/dependencies['packagesDir']/package['name']
        revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        if revision != package['rev']:
            raise ValueError(f'dependency revision differs from lock: {package["name"]}')
        subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD', '--'], check=True)
    files = []
    for path in sorted(ROOT.rglob('*')):
        relative = path.relative_to(ROOT)
        if not path.is_file() or any(p in {'.lake', '.git', '__pycache__', 'work'} for p in relative.parts):
            continue
        if path.name.startswith('.check.') or path.name in {'.DS_Store', 'failed.log'}:
            continue
        if path.suffix in {'.olean', '.ilean', '.trace', '.pyc'}:
            continue
        files.append(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in files:
            archive.write(path, Path('PlanarNikodym')/path.relative_to(ROOT))
    with zipfile.ZipFile(output) as archive:
        if archive.testzip() is not None:
            raise ValueError('archive CRC validation failed')
        for path in files:
            if archive.read(str(Path('PlanarNikodym')/path.relative_to(ROOT))) != path.read_bytes():
                raise ValueError(f'archive content differs: {path}')
    digest = sha256(output.read_bytes())
    output.with_suffix(output.suffix+'.sha256').write_text(f'{digest}  {output.name}\n')
    print(json.dumps({'archive': str(output), 'files': len(files), 'bytes': output.stat().st_size,
                      'sha256': digest, 'clean_locked_dependencies': len(dependencies['packages']),
                      'library_modules': summary['library_modules'],
                      'audited_declarations': summary['audited_declarations'],
                      'audited_theorems': summary['audited_theorems']}, indent=2))

if __name__ == '__main__':
    main()
