"""Collect the relay evidence (run in WSL with python3 -I -B after build, comparator, export, kernels).
Writes evidence/{BUILD,COMPARATOR,KERNEL-REPLAY,AXIOM-AUDIT,SOURCE-AUDIT,CHOICES,ORIGINAL-SOURCE,
BINARY-DIGESTS,DEPENDENCY-CHECK}.json, evidence/AXIOMS.txt and evidence/PORT.diff."""
from pathlib import Path
import hashlib, json, re, subprocess, os, time

D = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11')
P, O, E, R, K = D / 'project', D / 'original', D / 'evidence', D / 'results', D / 'kernels'
E.mkdir(exist_ok=True)
COMMIT = 'f475c200b1fe55d01dcb1e582bd910fcc01ab2bc'
ML = '56a005855ea17e0b0958f73ec801ae140b0a1679'


def sha_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def dump(name, obj):
    (E / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


version = subprocess.check_output([str(D / 'toolchain/bin/lean'), '--version'], text=True).strip()
mods = json.loads((P / 'scripts/modules.json').read_text())
pkg_mods = mods + ['Challenge', 'Solution', 'Audit']

# ---------------- BUILD.json
hist = [json.loads(l) for l in (P / '.lake/replay/history.ndjson').read_text().splitlines() if l.strip()]
nport = len([l for l in (D / 'attempts/history-port-attempts.ndjson').read_text().splitlines() if l.strip()])
fresh = hist[nport:]
final = {}
for r in fresh:
    if r['exit'] == 0:
        final[r['module']] = r
missing = [m for m in pkg_mods if m not in final]
cache = json.loads((P / '.lake/replay/completed.json').read_text())
build = {
    'status': 'PASS' if not missing and all(m in cache for m in pkg_mods) else 'FAIL',
    'lean_version': version, 'mathlib_commit': ML,
    'project_modules': len(mods), 'package_modules': len(pkg_mods),
    'one_compiler_at_a_time': True, 'lean_heap_MiB': 6144, 'lean_threads': 1, 'timeout_seconds_per_module': 1800,
    'linux_process_tree_stop_rss_bytes': 9000000000,
    'peak_observed_tree_rss_bytes': max(r['peak_tree_bytes'] for r in hist),
    'minimum_available_before_build_bytes': min(r['free_before_bytes'] for r in hist),
    'memory_floor_bytes': 8 * 1024 ** 3,
    'module_options': {'UndecidablePhaseDiagram.Statements': ['-Dbackward.isDefEq.respectTransparency=false']},
    'records_note': 'Each peak is the cumulative process-tree peak of its serial replay invocation, hence an upper bound for the module. The port was done by resumed serial replays (port_history, including every failed attempt); the final record is one fresh full serial replay of all package modules from scratch (no --resume), final_by_module. free_before_bytes = min(Linux MemAvailable, Windows host heartbeat ullAvailPhys).',
    'missing_modules': missing,
    'fresh_full_replay_records': len(fresh),
    'fresh_full_replay_all_exit_0': all(r['exit'] == 0 for r in fresh),
    'fresh_full_replay_seconds_total': round(sum(r['seconds'] for r in fresh), 3),
    'final_by_module': {m: final[m] for m in pkg_mods if m in final},
    'port_attempts': nport, 'port_failed_attempts': sum(1 for r in hist[:nport] if r['exit'] != 0),
    'port_history': hist[:nport],
}
dump('BUILD.json', build)

# ---------------- COMPARATOR.json
cr = json.loads((R / 'comparator-receipt.json').read_text())
inv = [json.loads(l) for l in (D / 'bwrap-invocations.ndjson').read_text().splitlines() if l.strip()]
cfg = json.loads((P / 'comparator.json').read_text())
log = (R / 'comparator.log').read_text(errors='replace')
challenge = (P / 'Challenge.lean').read_text(encoding='utf-8')
cimps = re.findall(r'^import\s+(\S+)', challenge, re.M)
cr.update({
    'date_client': time.strftime('%Y-%m-%d'), 'mathlib_commit': ML,
    'comparator_command': 'lake comparator --config comparator.json',
    'theorem_names': cfg['theorem_names'], 'permitted_axioms': cfg['permitted_axioms'],
    'sandbox_observed': len(inv) > 0 and all('--unshare-all' in i['arguments'] for i in inv),
    'sandbox_invocations': len(inv),
    'sandbox_network_shared_invocations': sum('--share-net' in i['arguments'] for i in inv),
    'sandbox_invocation_commands': [i['arguments'][i['arguments'].index('--') + 1:] for i in inv],
    'default_kernel_accepts': 'Lean default kernel accepts the solution' in log,
    'comparator_verdict_line': 'Your solution is okay!' if 'Your solution is okay!' in log else None,
    'challenge_imports': cimps, 'challenge_imports_only_mathlib': all(i.startswith('Mathlib.') for i in cimps),
    'challenge_sha256': sha_file(P / 'Challenge.lean'), 'solution_sha256': sha_file(P / 'Solution.lean'),
    'transparent_definition_copy': True,
    'log': 'results/comparator.log', 'sandbox_invocation_log': 'bwrap-invocations.ndjson',
})
dump('COMPARATOR.json', cr)

# ---------------- KERNEL-REPLAY.json
xr = json.loads((R / 'export-receipt.json').read_text())
kr = {'export_sha256': xr['sha256'], 'export_bytes': xr['bytes'], 'export_receipt': 'results/export-receipt.json',
      'export_command': xr['command'], 'export_seconds': xr['seconds'], 'export_peak_tree_rss_bytes': xr['peak_tree_rss_bytes'],
      'roots': xr['roots'], 'kernel_replays': {}}
for k in ('leanchecker', 'nanoda'):
    p = K / (k + '-receipt.json')
    if p.exists():
        kr['kernel_replays'][k] = json.loads(p.read_text())
kr['note'] = ('Both replays use the Linux binaries of the pinned toolchain (the forgetting relay\'s Windows binaries live in a '
              'directory this relay may not read). Each runs serially under the process-tree RSS watchdog (stop at 9.0 GB, '
              'below the forgetting relay\'s 9.9 GB cap). nanoda runs with num_threads 1 (serial on the main thread) and a '
              '128 MiB main-thread stack (RLIMIT_STACK), the stack of the forgetting relay\'s stack-reserve nanoda build.')
kr['status'] = 'PASS' if all(kr['kernel_replays'].get(k, {}).get('exit') == 0 for k in ('leanchecker', 'nanoda')) else 'FAIL'
dump('KERNEL-REPLAY.json', kr)

# ---------------- AXIOMS.txt / AXIOM-AUDIT.json
ax = (P / 'AXIOMS.txt').read_text(encoding='utf-8')
(E / 'AXIOMS.txt').write_text(ax, encoding='utf-8')
decls = [(lambda x: [x[0], x[1][0], x[1][1]])(json.loads(l.split('UPD_DECL:', 1)[1]))
         for l in ax.splitlines() if l.startswith('UPD_DECL:')]
count = int(re.search(r'UPD_DECL_COUNT:(\d+)', ax).group(1))
roots = re.findall(r'^#print axioms (\S+)$', (P / 'Audit.lean').read_text(encoding='utf-8'), re.M)
std = {'propext', 'Classical.choice', 'Quot.sound'}
printed = dict(re.findall(r"^'?([^'\s]+)'? depends on axioms: \[([^\]]*)\]", ax, re.M))
final_axioms = {}
for n in ['UPD.theorem_A', 'UPD.corollary_B', 'UPD.existsUniversal']:
    final_axioms[n] = [a.strip() for a in printed.get(n, '').split(',') if a.strip()]
bad = [d for d in decls if not set(d[2]) <= std]
dump('AXIOM-AUDIT.json', {
    'status': 'PASS' if not bad and count == len(decls) and 'UPD_FINAL_TYPES_OK' in ax else 'FAIL',
    'permitted_axioms': sorted(std), 'final_theorem_axioms': final_axioms,
    'final_theorem_types_checked': 'UPD_FINAL_TYPES_OK' in ax,
    'explicit_print_axioms_roots': roots, 'explicit_roots_count': len(roots),
    'all_imported_project_declarations_count': count, 'including_generated_and_private': True,
    'private_declarations': sum(1 for d in decls if d[0].startswith('_private')),
    'declarations_without_axioms': sum(1 for d in decls if not d[2]),
    'unexpected': bad,
    'declarations': decls, 'axioms_text_sha256': sha_file(E / 'AXIOMS.txt'), 'source_census': 'SOURCE-AUDIT.json'})

# ---------------- SOURCE-AUDIT.json
lean_files = sorted([p for p in P.rglob('*.lean') if 'vendor' not in p.parts and '.lake' not in p.parts])
forb = re.compile(r'(^|[^`])(native_decide|implemented_by|@\[extern)|^[ \t]*axiom[ \t]|(^|[^`])autoImplicit[ \t]+true|decide[ \t]+\+native', re.M)
hits, sorries, noimp = [], [], []
for p in lean_files:
    t = p.read_text(encoding='utf-8')
    rel = str(p.relative_to(P))
    for m in forb.finditer(t):
        hits.append({'file': rel, 'line': t[:m.start()].count('\n') + 1, 'text': m.group(0).strip()})
    for m in re.finditer(r'\bsorry\b', t):
        sorries.append({'file': rel, 'line': t[:m.start()].count('\n') + 1})
    if 'set_option autoImplicit false' not in t:
        noimp.append(rel)
ro = {}
for path in ['/opt/forgetting-arxiv-2026-11-10', '/opt/forgetting-arxiv-2026-11-10-runtime.tar.zst',
             '/opt/forgetting-arxiv-2026-11-10-runtime.tar.json', '/opt/package-forgetting-arxiv.py', '/home/lean']:
    out = subprocess.run(['find', path, '-newermt', '2026-11-11 09:00:00', '-print'], capture_output=True, text=True)
    ro[path] = out.stdout.split()
lint = subprocess.run(['bash', 'scripts/lint.sh'], cwd=P, capture_output=True, text=True)
dump('SOURCE-AUDIT.json', {
    'lean_files_checked': [str(p.relative_to(P)) for p in lean_files],
    'forbidden_constructs': hits, 'sorry_tokens': sorries,
    'sorry_only_in_challenge_holes': all(s['file'] == 'Challenge.lean' for s in sorries) and len(sorries) == 3,
    'files_without_autoImplicit_false': noimp,
    'lint_sh_output': lint.stdout.strip(), 'lint_sh_exit': lint.returncode,
    'read_only_inputs_modified_after_session_start': ro,
    'read_only_inputs_note': 'find -newermt "2026-11-11 09:00:00" (this relay started at 09:18 WSL time) over the forgetting relay, its runtime archive and receipt, its packaging script and /home/lean: empty lists mean no file there was created or modified during this relay.',
})

# ---------------- CHOICES.json, ORIGINAL-SOURCE.json
ch = []
for p in sorted(O.rglob('*.lean')):
    for i, l in enumerate(p.read_text(encoding='utf-8').splitlines(), 1):
        if '[choice]' in l:
            ch.append({'file': str(p.relative_to(O)), 'line': i, 'text': l.strip()})
dump('CHOICES.json', {'scope': 'Every [choice] occurrence in the original project Lean source (commit %s). The proof-side fidelity choices P-1 to P-51, the hypothesis choices H-1 to H-4 and QB\'s rulings are in STATUS.md and BLUEPRINT.md (Part D). Port-specific changes are in PORT.diff and REPORT.md; the port makes no new fidelity choice.' % COMMIT,
                      'count': len(ch), 'choices': ch})
dump('ORIGINAL-SOURCE.json', {'commit': COMMIT, 'files': [{'path': str(p.relative_to(O)), 'sha256': sha_file(p)} for p in sorted(O.rglob('*')) if p.is_file()]})

# ---------------- BINARY-DIGESTS.json
recs = []
for b in ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin']:
    p = D / 'toolchain/bin' / b
    recs.append({'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha_file(p),
                 'same_as_forgetting_relay_binary': sha_file(p) == sha_file(Path('/opt/forgetting-arxiv-2026-11-10/toolchain/bin') / b)})
p = D / 'bubblewrap/usr/bin/bwrap'
recs.append({'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha_file(p), 'same_as_forgetting_relay_binary': sha_file(p) == sha_file(Path('/opt/forgetting-arxiv-2026-11-10/bubblewrap/usr/bin/bwrap'))})
dump('BINARY-DIGESTS.json', {'records': recs, 'toolchain': 'cp -a of /opt/forgetting-arxiv-2026-11-10/toolchain (Lean 4.35.0, eb6cafb7290e8bd5f2937522d8d804f58f02bafc)'})

# ---------------- DEPENDENCY-CHECK.json (computed at staging)
(E / 'DEPENDENCY-CHECK.json').write_bytes((P / 'DEPENDENCY-CHECK.json').read_bytes())

# ---------------- PORT.diff (original Lean sources vs ported)
diff = []
for p in sorted(O.rglob('*.lean')):
    rel = p.relative_to(O)
    q = P / rel
    r = subprocess.run(['diff', '-u', '--label', f'original/{rel}', '--label', f'ported/{rel}', str(p), str(q)], capture_output=True, text=True)
    diff.append(r.stdout)
(E / 'PORT.diff').write_text(''.join(diff), encoding='utf-8')
print('evidence written:', sorted(x.name for x in E.iterdir()))
print('BUILD', build['status'], 'COMPARATOR exit', cr['exit'], 'KERNELS', kr['status'], 'AXIOMS decls', count, 'bad', len(bad))
