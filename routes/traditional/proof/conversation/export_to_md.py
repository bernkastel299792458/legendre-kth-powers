"""把 Claude 桌面版导出的会话 transcript.jsonl 转成可读的 Markdown。
用法：python -I export_to_md.py <transcript.jsonl> <out.md>
保留：用户消息（去掉系统注入的 <system-reminder> 等）、助手的文字回答；
工具调用只保留一行摘要（工具名 + 描述），工具输出与内部思考不保留（完整记录见导出的 zip）。"""
import json
import re
import sys

src, out = sys.argv[1], sys.argv[2]
MIDTURN_NOTE = chr(10) * 2 + '*（用户在助手工作过程中发送的消息）*'
REMINDER = re.compile(r'<system-reminder>.*?</system-reminder>', re.S)
MIDTURN = re.compile(r'The user sent a new message while you were working:\s*(.*?)\s*(?:This is how Claude Code surfaces|$)', re.S)


def is_system_text(t):
    t = t.lstrip()
    return t.startswith('<task-notification') or '[SYSTEM NOTIFICATION' in t[:200]


def clean_user(t):
    if is_system_text(t):
        return ''
    t = REMINDER.sub('', t)
    t = re.sub(r'<task-notification>.*?</task-notification>', '', t, flags=re.S)
    t = re.sub(r'<(command-[a-z-]+|local-command-[a-z-]+)>.*?</\1>', '', t, flags=re.S)
    return t.strip()


def tool_line(b):
    inp = b.get('input') or {}
    name = b.get('name', '')
    desc = inp.get('description') or inp.get('title') or inp.get('query') or inp.get('file_path') or ''
    short = name.split('__')[-1]
    return f'- *[工具调用 {short}]* {desc}'.rstrip()


rows = []
seen = set()
with open(src, encoding='utf-8') as f:
    for line in f:
        try:
            o = json.loads(line)
        except Exception:
            continue
        t = o.get('type')
        if t == 'attachment' and not o.get('isSidechain'):
            a = o.get('attachment') or {}
            if a.get('type') == 'queued_command':
                txt = clean_user(str(a.get('prompt') or ''))
                if txt and txt not in seen:
                    seen.add(txt)
                    rows.append(('user', txt + MIDTURN_NOTE))
            continue
        if t not in ('user', 'assistant') or o.get('isSidechain'):
            continue
        m = o.get('message') or {}
        c = m.get('content')
        if t == 'user':
            if isinstance(c, str):
                txt = clean_user(c)
                if txt and txt not in seen:
                    seen.add(txt)
                    rows.append(('user', txt))
            elif isinstance(c, list):
                for b in c:
                    if b.get('type') == 'text':
                        txt = clean_user(b.get('text', ''))
                        if txt and txt not in seen:
                            seen.add(txt)
                            rows.append(('user', txt))
                    elif b.get('type') == 'tool_result':
                        cc = b.get('content')
                        s = cc if isinstance(cc, str) else ' '.join(x.get('text', '') for x in (cc or []) if isinstance(x, dict))
                        mm = MIDTURN.search(s or '')
                        if mm and mm.group(1).strip() and mm.group(1).strip() not in seen:
                            seen.add(mm.group(1).strip())
                            rows.append(('user', mm.group(1).strip() + '\n\n*（用户在助手工作过程中发送的消息）*'))
        else:
            if isinstance(c, list):
                for b in c:
                    if b.get('type') == 'text' and b.get('text', '').strip():
                        rows.append(('assistant', b['text'].strip()))
                    elif b.get('type') == 'tool_use':
                        rows.append(('tool', tool_line(b)))

# 合并相邻的同角色块
merged = []
for r, txt in rows:
    if merged and merged[-1][0] == r and r in ('assistant', 'tool'):
        merged[-1] = (r, merged[-1][1] + '\n' + txt) if r == 'tool' else (r, merged[-1][1] + '\n\n' + txt)
    elif merged and r == 'tool' and merged[-1][0] == 'assistant':
        merged.append((r, txt))
    else:
        merged.append((r, txt))

with open(out, 'w', encoding='utf-8') as f:
    f.write('# 对话记录：勒让德猜想与相邻 k 次方之间的素数（k ≥ 67）\n\n')
    f.write('*由 Claude 桌面版导出的会话记录自动转换（`export_to_md.py`）。保留用户消息与助手的文字回答；'
            '工具调用只保留一行摘要，工具输出与内部思考未保留。原始完整记录见导出的 zip。*\n\n---\n\n')
    turn = 0
    for r, txt in merged:
        if r == 'user':
            turn += 1
            f.write(f'## 用户（第 {turn} 轮）\n\n{txt}\n\n')
        elif r == 'assistant':
            f.write(f'### 助手\n\n{txt}\n\n')
        else:
            f.write(f'<details><summary>工具调用摘要</summary>\n\n{txt}\n\n</details>\n\n')
print('turns:', turn, 'blocks:', len(merged))
