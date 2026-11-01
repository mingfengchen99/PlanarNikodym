#!/usr/bin/env python3
"""Read-only project health inventory; optional JSON report, without claiming mathematical completion."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess
from check_layout import ROOT, modules, source_manifest, source_digest


def masked_lean(text, mask_strings=False):
    """Preserve line positions while masking nested comments and optionally strings."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        ch = text[i]
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/':
                depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if ch == '\n' else ' '); i += 1; continue
        if string:
            if ch == '\\' and i + 1 < len(text):
                out.extend('  ' if mask_strings else text[i:i+2]); i += 2; continue
            if ch == '"':
                string = False
            out.append(('\n' if ch == '\n' else ' ') if mask_strings else ch)
            i += 1; continue
        if pair == '/-':
            depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i)); i = end; continue
        if ch == '"':
            string = True
        out.append(' ' if mask_strings and ch == '"' else ch); i += 1
    return ''.join(out)


def command(*args):
    return subprocess.run(args, text=True, capture_output=True, check=False)


def inventory(baseline=None):
    library = modules()
    files = sorted(set(library.values()) | {ROOT/'Audit.lean'})
    counts, by_group, scans, options = Counter(), {}, {}, []
    patterns = {
        'sorry_admit_sorryAx': r'\b(?:sorry|admit|sorryAx)\b',
        'project_axiom': r'^\s*(?:private\s+)?axiom\s',
        'unsafe': r'\bunsafe\b',
        'native_decide': r'\bnative_decide\b',
        'extern_implemented_by': r'\b(?:extern|implemented_by)\b',
        'autoImplicit_true': r'set_option\s+autoImplicit\s+true\b',
        'unlimited_resources': r'set_option\s+(?:maxHeartbeats|maxRecDepth)\s+0\b',
        'disabled_linter': r'set_option\s+linter\.[\w.]+\s+false\b',
    }
    lengths, imports, rows = [], {}, []
    for f in files:
        rel = str(f.relative_to(ROOT)); text = f.read_text()
        plain = masked_lean(text); code = masked_lean(text, True)
        count = Counter(files=1, lines=len(text.splitlines()))
        for original, cleaned in zip(text.splitlines(), plain.splitlines()):
            count['blank' if not original.strip() else 'comment_only' if not cleaned.strip() else 'code'] += 1
        counts.update(count)
        group = rel.split('/')[1] if rel.startswith('PlanarNikodym/') else rel
        by_group.setdefault(group, Counter()).update(count)
        lengths.append(count['lines']); rows.append({'file':rel,'lines':count['lines']})
        for name, pattern in patterns.items():
            for m in re.finditer(pattern, code, re.M):
                scans.setdefault(name, []).append({'file':rel,'line':code.count('\n',0,m.start())+1})
        for m in re.finditer(r'set_option\s+(maxHeartbeats|maxRecDepth)\s+(\d+)', code):
            options.append({'file':rel,'option':m[1],'value':int(m[2])})
        imports[rel] = re.findall(r'^import (PlanarNikodym(?:\.[A-Za-z0-9_]+)*)\s*$',code,re.M)
    duplicate = {f:sorted(k for k,v in Counter(names).items() if v>1) for f,names in imports.items()}
    duplicate = {f:v for f,v in duplicate.items() if v}
    lock = json.loads((ROOT/'lake-manifest.json').read_text())
    dependencies = []
    for package in lock['packages']:
        path = ROOT/lock['packagesDir']/package['name']
        rev = command('git','-C',str(path),'rev-parse','HEAD')
        dirty = command('git','-C',str(path),'diff','--quiet','HEAD','--')
        untracked = command('git','-C',str(path),'ls-files','--others','--exclude-standard')
        dependencies.append({'name':package['name'],'locked':package['rev'],
            'actual':rev.stdout.strip(),'revision_matches':rev.returncode==0 and rev.stdout.strip()==package['rev'],
            'tracked_clean':dirty.returncode==0,'untracked_files':untracked.stdout.splitlines(),
            'untracked_check_ok':untracked.returncode==0})
    current = source_manifest()
    saved = json.loads((ROOT/'verification/source-manifest.json').read_text())
    result = {'collected_at_utc':datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'scope':'All project Lean sources including root and Audit; thematic directories are shared, not exclusively D.',
        'library_modules':len(library),'lean_files':len(files),'line_counts':dict(counts),
        'by_group':{k:dict(v) for k,v in sorted(by_group.items())},
        'line_median':statistics.median(lengths),'largest_files':sorted(rows,key=lambda r:-r['lines'])[:10],
        'hazards':{k:scans.get(k,[]) for k in patterns},'resource_options':options,
        'duplicate_local_imports':duplicate,'dependencies':dependencies,
        'source_digest':source_digest(current),
        'formal_manifest_mismatches':sorted(k for k in set(saved)|set(current) if saved.get(k)!=current.get(k)),
        'formal_summary':json.loads((ROOT/'verification/summary.json').read_text())}
    if baseline:
        old=json.loads(baseline.read_text())
        result['baseline_comparison']={
            'changed':sorted(k for k,v in old.items() if current.get(k)!=v and k in current),
            'missing':sorted(set(old)-set(current)), 'added_to_manifest':sorted(set(current)-set(old)),
            'all_library_modules_preserved':all(current.get(k)==v for k,v in old.items() if k=='PlanarNikodym.lean' or k.startswith('PlanarNikodym/'))}
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=inventory(args.baseline)
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('library_modules','lean_files','line_counts','line_median','duplicate_local_imports','hazards')},ensure_ascii=False,indent=2))
    if any(result['hazards'].values()) or result['duplicate_local_imports'] or any(
        not d['revision_matches'] or not d['tracked_clean'] or not d['untracked_check_ok'] or d['untracked_files']
        for d in result['dependencies']):
        raise SystemExit(1)

if __name__=='__main__':
    main()
