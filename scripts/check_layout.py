#!/usr/bin/env python3
"""Check project imports, module index and documentation; record a successful Lean audit."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parent.parent
GENERATED = {ROOT/'verification'/name for name in
             ('check.log', 'summary.json', 'source-manifest.json')}
GROUPS = {
    'Core': '定义、主结论与基础测度', 'Rank': '函数秩、Wronskian 与泛型秩',
    'Geometry': '解析坐标、测度和几何工具', 'Reduction': '参数消去与降维',
    'Classification': '常秩与一般分类的推导', 'Cells': '胞腔接口与条件式分解',
    'Tame': 'R_an 可定义性语义、解析图、种子与参数变换',
    'Projection': '投影模型、输入与传递', 'Avoidance': '有限 jet、覆盖与完整避场',
    'Analysis/Fourier': '频率截断、Fourier 核与卷积',
    'Analysis/Sobolev': '尺度 Sobolev 与实际频带正则性',
    'Analysis/Localization': '解析截断与有限局部化',
    'Analysis/Jets': '平均的求导、完整 jet 与有限振幅',
    'Analysis/Maximal': '平均、最大估计、求和及分类连接',
    'Examples': '各阶段实例与边界核对',
}

def sha256(data):
    return hashlib.sha256(data).hexdigest()

def modules():
    paths = [ROOT/'PlanarNikodym.lean'] + sorted((ROOT/'PlanarNikodym').rglob('*.lean'))
    return {str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p for p in paths}

def source_manifest():
    paths = list(modules().values()) + [ROOT/name for name in
        ('Audit.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
         'scripts/check.sh', 'scripts/check_layout.py', 'scripts/package.py', 'scripts/audit_health.py')]
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()) for p in sorted(paths)}

def source_digest(manifest):
    return sha256(json.dumps(manifest, sort_keys=True, separators=(',', ':')).encode())

def index_text(library):
    lines = ['# 模块索引', '', '由 `python3 scripts/check_layout.py --write-index` 生成。', '',
             '统一入口为 [PlanarNikodym.lean](../PlanarNikodym.lean)。'
             '目录按主题分组；跨组依赖由实际 import 表达，不表示严格的层级关系。', '',
             f'当前共 {len(library)} 个库模块，其中 {len(library)-1} 个证明／定义模块。', '']
    grouped = {}
    for name, path in library.items():
        if name != 'PlanarNikodym':
            group = str(path.parent.relative_to(ROOT/'PlanarNikodym'))
            grouped.setdefault(group, []).append(path)
    ordered_groups = [g for g in GROUPS if g in grouped] + sorted(set(grouped)-set(GROUPS))
    for group in ordered_groups:
        paths = sorted(grouped[group])
        lines.extend([f'## {group}（{len(paths)}）', '', GROUPS.get(group, group), ''])
        lines.extend(f'- [{p.stem}](../{p.relative_to(ROOT)})' for p in paths)
        lines.append('')
    return '\n'.join(lines)

def check_layout(write_index=False, check_migration=False):
    library = modules()
    graph = {}
    for name, path in library.items():
        imports = re.findall(r'^import (PlanarNikodym(?:\.[A-Za-z0-9_]+)*)\s*$',
                             path.read_text(), re.MULTILINE)
        for dependency in imports:
            if dependency not in library:
                raise ValueError(f'{path.relative_to(ROOT)}: missing import {dependency}')
        graph[name] = imports
    visited, active = set(), set()
    def visit(name):
        if name in active:
            raise ValueError(f'import cycle at {name}')
        if name in visited:
            return
        active.add(name)
        for dependency in graph[name]:
            visit(dependency)
        active.remove(name)
        visited.add(name)
    visit('PlanarNikodym')
    if visited != set(library):
        raise ValueError(f'unreachable modules: {sorted(set(library)-visited)}')

    index = ROOT/'docs'/'MODULE_INDEX.md'
    expected = index_text(library)
    if write_index:
        index.write_text(expected)
    if not index.is_file() or index.read_text() != expected:
        raise ValueError('module index is stale; run python3 scripts/check_layout.py --write-index')

    documents = sorted(ROOT.glob('*.md')) + sorted((ROOT/'docs').rglob('*.md')) + [ROOT/'verification'/'README.md']
    link_count = 0
    for document in documents:
        for target in re.findall(r'\]\(([^)]+)\)', document.read_text()):
            if '://' in target or target.startswith('#') or target.startswith('mailto:'):
                continue
            target = unquote(target.split('#', 1)[0].strip('<>'))
            path = (document.parent/target).resolve()
            if ROOT not in path.parents:
                raise ValueError(f'{document.relative_to(ROOT)}: link escapes the packaged project: {target}')
            if not path.is_file() and path not in GENERATED:
                raise ValueError(f'{document.relative_to(ROOT)}: broken link {target}')
            link_count += 1
    if check_migration:
        report = json.loads((ROOT/'verification'/'reorganization.json').read_text())
        for move in report['module_moves']:
            source = (ROOT/move['new_path']).read_text()
            body = re.sub(r'^import [^\n]+\n', '', source, flags=re.MULTILINE)
            if sha256(body.encode()) != move['proof_body_sha256']:
                raise ValueError(f'proof body changed during reorganization: {move["new_path"]}')
        if sha256((ROOT/'Audit.lean').read_bytes()) != report['audit_source_sha256']:
            raise ValueError('Audit.lean changed during reorganization')
        print(f'Reorganization verified: {len(report["module_moves"])} proof bodies and Audit.lean preserved.')
    print(f'Layout verified: {len(library)} library modules, all reachable; {link_count} local document links.')
    return len(library), link_count

def record(log_path):
    content = log_path.read_text()
    audit = re.search(r'Audited (\d+) project declarations \((\d+) theorems\):', content)
    jobs = re.search(r'Build completed successfully \((\d+) jobs\).', content)
    module_audit = re.search(r'Module origin audit: (\d+) declarations \((\d+) theorems\); (\d+) outside namespace \((\d+) theorems\); (\d+) project modules\.', content)
    if not audit or not jobs or not module_audit or re.search(r'\b(?:warning|error):', content, re.IGNORECASE):
        raise ValueError('a complete build and audit without warnings or errors is required')
    if int(module_audit[5]) != len(modules()):
        raise ValueError('module-origin audit did not cover every project module')
    manifest = source_manifest()
    summary = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(timespec='seconds'),
        'lean_toolchain': (ROOT/'lean-toolchain').read_text().strip(),
        'library_modules': len(modules()), 'build_jobs': int(jobs[1]),
        'audited_declarations': int(audit[1]), 'audited_theorems': int(audit[2]),
        'module_origin_declarations': int(module_audit[1]),
        'module_origin_theorems': int(module_audit[2]),
        'outside_namespace_declarations': int(module_audit[3]),
        'outside_namespace_theorems': int(module_audit[4]),
        'module_origin_modules': int(module_audit[5]),
        'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'source_digest': source_digest(manifest), 'check_log_sha256': sha256(log_path.read_bytes()),
        'log': 'verification/check.log',
    }
    (ROOT/'verification'/'source-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    (ROOT/'verification'/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(f'Verification recorded: {audit[1]} declarations, {audit[2]} theorems.')

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-index', action='store_true')
    parser.add_argument('--check-migration', action='store_true', help='verify the one-time reorganization baseline')
    parser.add_argument('--record', type=Path, help='record a successful Lean build/audit log')
    args = parser.parse_args()
    check_layout(args.write_index, args.check_migration)
    if args.record:
        record(args.record)

if __name__ == '__main__':
    main()
