#!/usr/bin/env python3
"""Token use of this checkout's agent sessions, from local Claude Code and Codex transcripts.

usage: token_usage.py [--since YYYY-MM] [--repo PATH] breakdown|capsim

breakdown: cost by token type, by what each step did, and by context size.
capsim:    replay the sessions with an auto-compaction cap (100k/150k/200k) against a matched no-cap run.
Cost is billable-equivalent input tokens: cache read 0.1, cache write 1.25, output 5.
Reads ~/.claude/projects and ~/.codex/sessions only; prints aggregates, never transcript text.
"""
import argparse, collections, glob, json, os, re, subprocess


def w(u):
    return u['inp'] + 0.1 * u['cr'] + 1.25 * u['cw'] + 5 * u['out']


def claude(repo):
    key = re.sub(r'[^A-Za-z0-9]', '-', repo)
    for f in sorted(glob.glob(os.path.expanduser(f'~/.claude/projects/{key}*/**/*.jsonl'), recursive=True)):
        steps, byreq = [], {}
        for line in open(f, errors='replace'):
            if '"type":"assistant"' not in line:
                continue
            d = json.loads(line)
            m = d.get('message') or {}
            rid = d.get('requestId') or d.get('uuid')
            if rid not in byreq:
                u = m.get('usage') or {}
                byreq[rid] = {'u': {'inp': u.get('input_tokens', 0), 'cr': u.get('cache_read_input_tokens', 0),
                                    'cw': u.get('cache_creation_input_tokens', 0), 'out': u.get('output_tokens', 0)},
                              'calls': []}
                steps.append(byreq[rid])
            for c in m.get('content') or []:
                if c.get('type') == 'tool_use':
                    byreq[rid]['calls'].append((c['name'], json.dumps(c.get('input'))))
        if steps:
            yield steps


def codex(repo, since):
    for f in sorted(glob.glob(os.path.expanduser('~/.codex/sessions/*/*/*/*.jsonl'))):
        if '/'.join(f.split('/')[-4:-2]) < since.replace('-', '/'):
            continue
        steps, cur = [], {'calls': []}
        for i, line in enumerate(open(f, errors='replace')):
            if i == 0 and repo not in line:
                break
            head = line[:400]
            if '"custom_tool_call"' in head or '"function_call"' in head:
                p = json.loads(line)['payload']
                cur['calls'].append((p.get('name') or '', str(p.get('input') or p.get('arguments'))))
            elif '"token_count"' in head:
                info = json.loads(line)['payload'].get('info')
                if info:
                    lu = info['last_token_usage']
                    cr = lu.get('cached_input_tokens', 0)
                    cur['u'] = {'inp': lu['input_tokens'] - cr, 'cr': cr, 'cw': 0, 'out': lu['output_tokens']}
                    steps.append(cur)
                    cur = {'calls': []}
        if steps:
            yield steps


def kind(n, i):
    if re.search(r'lean_diagnostic|lean_build|lean_verify|lake build|lake env lean|gate\.sh', n + i):
        return 'lean check'
    if re.match(r'Grep|Glob', n) or re.search(r'lean_(local_search|references|declaration)', n) \
            or re.search(r'(^|[\s;&|"])(rg|grep|git grep)\s', i):
        return 'search'
    if n == 'Read' or re.search(r'(^|[\s;&|"])(sed -n|cat|head|tail|nl)\s', i) or 'context-pack' in i:
        return 'read file'
    if re.match(r'Edit|Write|MultiEdit', n) or 'apply_patch' in i[:200] or 'sed -i' in i:
        return 'edit'
    return 'other tool'


def breakdown(S):
    T = sum(w(st['u']) for s in S for st in s)
    parts, acts, size = collections.Counter(), collections.Counter(), collections.Counter()
    for s in S:
        for st in s:
            u = st['u']
            parts['fresh input'] += u['inp']; parts['cache read'] += 0.1 * u['cr']
            parts['cache write'] += 1.25 * u['cw']; parts['output'] += 5 * u['out']
            ks = [kind(n or '', i) for n, i in st['calls']] or ['no tool']
            for k in ks:
                acts[k] += w(u) / len(ks)
            size[min((u['inp'] + u['cr'] + u['cw']) // 100000, 9)] += w(u)
    print(f'{len(S)} sessions, {sum(map(len, S))} steps, {T / 1e6:.0f}M')
    for name, c in (('token type', parts), ('activity', acts)):
        print(name + ':', ', '.join(f'{k} {100 * v / T:.0f}%' for k, v in c.most_common()))
    print('context:', ', '.join(f'{k * 100}k+ {100 * v / T:.0f}%' for k, v in sorted(size.items())))


def replay(S, cap, kept=20000, sumout=4000):
    tot = n = 0
    for s in S:
        prev, ctx_sim = None, 0
        for st in s:
            u = st['u']; ctx = u['inp'] + u['cr'] + u['cw']
            if prev is None or ctx < prev * 0.5:
                delta, ctx_sim = ctx, 0
            else:
                delta = max(ctx - prev, 0)
            prev = ctx
            ctx_sim += delta
            if ctx_sim > cap:
                tot += 0.1 * ctx_sim + 5 * sumout; n += 1
                ctx_sim = kept + min(delta, cap // 4); tot += 1.25 * ctx_sim
            else:
                tot += 0.1 * (ctx_sim - delta) + 1.25 * delta
            tot += 5 * u['out']
    return tot, n


def capsim(S):
    base, _ = replay(S, 10 ** 12)
    print(f'no cap {base / 1e6:.0f}M')
    for cap in (100000, 150000, 200000):
        for kept in (20000, 60000):
            t, n = replay(S, cap, kept)
            print(f'cap {cap // 1000}k, {kept // 1000}k kept: {100 * (1 - t / base):.0f}% less, {n} compactions')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--since', default='2026-10')
    ap.add_argument('--repo', default=subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True,
                                                      text=True).stdout.strip().split('-worktrees')[0])
    ap.add_argument('mode', choices=['breakdown', 'capsim'])
    a = ap.parse_args()
    S = list(claude(a.repo)) + list(codex(a.repo, a.since))
    (breakdown if a.mode == 'breakdown' else capsim)(S)
