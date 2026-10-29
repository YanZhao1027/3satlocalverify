#!/usr/bin/env python3
"""Deterministic 10-gate research board and searchable JSONL evidence cards.

Canonical data: research/ten_gates.json.
This is RAG-ready local text, NOT a deployed vector DB or a background monitor.
"""
import argparse
from collections import Counter
from datetime import date
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "research/ten_gates.json"
OUTPUTS = (
    ROOT / "docs/RESEARCH_GATE_BOARD.md",
    ROOT / "research/AGENT_CONTEXT.md",
    ROOT / "research/gate_cards.jsonl",
)
STATES = {"open", "partial", "sample_verified", "passed"}
KINDS = {"lean_kernel", "kernel_audit", "runtime", "report"}
LABELS = {
    "open": "未通过",
    "partial": "部分证据，未过关",
    "sample_verified": "指定样例通过，非通用",
    "passed": "验收完成",
}
B = chr(96)


def validate(data, root=ROOT):
    assert data["schema_version"] == 1
    assert data["project"] == "YanZhao1027/3satlocalverify"
    date.fromisoformat(data["reviewed_on"])
    assert re.fullmatch("[0-9a-f]{40}", data["original_upstream_commit"])
    assert re.fullmatch("[0-9a-f]{40}", data["baseline_repo_commit"])
    assert len(data["gates"]) == 10
    assert set(data["status_definitions"]) == STATES
    assert len(data["review_triggers"]) >= 3 and len(data["review_protocol"]) >= 3

    evidence = {}
    for ev in data["evidence"]:
        assert re.fullmatch(r"EV-[0-9]{3}", ev["id"])
        assert ev["id"] not in evidence
        assert ev["kind"] in KINDS
        assert ev["claim"].strip() and ev["limit"].strip()
        path = Path(ev["path"])
        assert not path.is_absolute() and ".." not in path.parts
        assert (root / path).is_file(), ev["path"]
        evidence[ev["id"]] = ev

    dependencies = {}
    for n, g in enumerate(data["gates"], start=1):
        assert g["id"] == n and g["slug"] == f"G{n:02d}"
        assert g["title"].strip() and g["difficulty"].strip()
        assert g["status"] in STATES and g["priority"] in {"P0", "P1", "P2"}
        assert g["acceptance"] and all(x.strip() for x in g["acceptance"])
        assert g["next_action"].strip()
        assert g["evidence_ids"] and len(set(g["evidence_ids"])) == len(g["evidence_ids"])
        assert all(eid in evidence for eid in g["evidence_ids"])
        assert all(isinstance(pr, int) and pr > 0 for pr in g["related_prs"])
        assert len(set(g["depends_on"])) == len(g["depends_on"])
        assert all(isinstance(dep, int) and dep != n and 1 <= dep <= 10 for dep in g["depends_on"])
        assert date.fromisoformat(g["reviewed_on"]) <= date.fromisoformat(data["reviewed_on"])
        dependencies[n] = g["depends_on"]
        if g["status"] == "sample_verified":
            assert any(evidence[eid]["kind"] == "runtime" for eid in g["evidence_ids"])
        if g["status"] == "passed":
            closure = g["closure"]
            assert closure and closure["reviewed_by"] and closure["evidence_ids"]
            assert set(closure["evidence_ids"]).issubset(evidence)
            assert len(closure["acceptance_checks"]) == len(g["acceptance"])
            assert not g["blockers"]
        else:
            assert g["closure"] is None
            assert g["blockers"], g["slug"]
    def walk(x, visiting, done):
        assert x not in visiting, f"dependency cycle near G{x:02d}"
        if x in done:
            return
        for dep in dependencies[x]:
            walk(dep, visiting + [x], done)
        done.add(x)
    done = set()
    for x in dependencies:
        walk(x, [], done)
    return evidence


def link(ev):
    return f"[{ev['id']}](../{ev['path']})"


def board_text(d, evidence):
    counts = Counter(g["status"] for g in d["gates"])
    lines = [
        "# 3satlocalverify：十关研究看板（证据驱动）",
        "",
        f"**人工复核日期：{d['reviewed_on']}** · 上游固定提交：{B}{d['original_upstream_commit']}{B}",
        "",
        "单一可信源：[结构化清单](../research/ten_gates.json) · "
        "[检索卡片 JSONL](../research/gate_cards.jsonl) · "
        "[Agent 快速上下文](../research/AGENT_CONTEXT.md) · "
        "[人工复核日志](../research/REVIEW_LOG.md) · "
        "[方法限制](METHODS_AND_LIMITATIONS.md)",
        "",
        "这里的检索卡片是 **RAG-ready 语料，不是已经运行的向量数据库或后台自动监控系统**。",
        "",
        "## 总览",
        "",
        f"**完整验收：{counts['passed']}/10**；指定样例通过：{counts['sample_verified']}/10；"
        f"部分证据：{counts['partial']}/10；未通过：{counts['open']}/10。"
        " 不把局部样例当作通用完成，也不使用误导性的总百分比。",
        "",
        "| 关卡 | 项目 | 状态 | 首要缺口 | 优先级 |",
        "|:---:|---|---|---|:---:|"
    ]
    for g in d["gates"]:
        gap = g["blockers"][0] if g["blockers"] else "全部验收条件均已核实"
        lines.append(f"| [{g['slug']}](#g{g['id']:02d}) | {g['title']} | "
                     f"{LABELS[g['status']]} | {gap} | {g['priority']} |")
    lines += [
        "",
        "## 下一轮工作队列",
        "",
        "**两条主要工作线：** G01 的全局连接器与真实计量执行器的形式化闭环，以及 G05 的完整原版准备命令单程序运行。"
        " G04 已完成一个真实小样例的收尾，接下来补非退化输入；G08 与 G09 持续审计不可计算依赖和 TM2 资源。"
        " G02、G03 的成功样例也不能替代通用验收。",
        ""
    ]
    for g in d["gates"]:
        if g["priority"] == "P0" and g["status"] != "passed":
            lines.append(f"- **{g['slug']} {g['title']}**：{g['next_action']}")
    lines += ["", "## 每关的验收与可追溯证据", ""]
    for g in d["gates"]:
        lines += [
            f'<a id="g{g["id"]:02d}"></a>',
            f"### {g['slug']} · {g['title']}",
            "",
            f"**状态：{LABELS[g['status']]}** · 难度：{g['difficulty']} · "
            f"优先级：{g['priority']} · 上次复核：{g['reviewed_on']}",
            "",
            "**怎样才算通过**",
        ]
        for s in g["acceptance"]:
            lines.append(f"- {s}")
        lines += ["", "**目前证实的范围**"]
        for s in g["verified_scope"]:
            lines.append(f"- {s}")
        if not g["verified_scope"]:
            lines.append("- 无足以关闭本关的原版运行或定理证据。")
        lines += ["", "**未解决的阻塞**"]
        for s in g["blockers"]:
            lines.append(f"- {s}")
        if not g["blockers"]:
            lines.append("- 已在验收闭环记录中给出通过依据。")
        lines += ["", f"**下一步：** {g['next_action']}", "", "**证据索引及边界**"]
        for eid in g["evidence_ids"]:
            ev = evidence[eid]
            lines.append(f"- {link(ev)}（{ev['kind']}）：{ev['claim']}；**限制**：{ev['limit']}。")
        if g["related_prs"]:
            prs = " · ".join(f"[PR #{p}](https://github.com/YanZhao1027/3satlocalverify/pull/{p})"
                             for p in g["related_prs"])
            lines += ["", "**关联审阅：** " + prs]
        if g["depends_on"]:
            deps = " · ".join(f"[G{dep:02d}](#g{dep:02d})" for dep in g["depends_on"])
            lines += ["", "**依赖关卡：** " + deps]
        lines += ["", "---", ""]
    lines += ["## 状态维护流程", ""]
    for n, step in enumerate(d["review_protocol"], start=1):
        lines.append(f"{n}. {step}")
    lines += [
        "",
        "查询摘要： " + B + "python3 scripts/research_board.py --status" + B,
        "",
        "更新单一可信源后执行： " + B + "python3 scripts/research_board.py --write" + B,
        "",
        "交付前验证： " + B + "python3 scripts/research_board.py --check" + B,
        "",
        "**重要边界：未完成完整原版高查询 SAT/#SAT，未证明所有输入的次指数优势，也没有证明 ETH 错误。**",
        ""
    ]
    return "\n".join(lines)


def context_text(d):
    stats = Counter(g["status"] for g in d["gates"])
    lines = [
        "# 研究 Agent 快速检索入口",
        "",
        f"复核日期 {d['reviewed_on']} · 上游版本 {d['original_upstream_commit']}",
        "",
        "打开 docs/RESEARCH_GATE_BOARD.md 与 research/ten_gates.json 可获得全部十关的验收条件、"
        "原始证据与局限。不要只看此页的结论。",
        "",
        f"完整通过 {stats['passed']}；样例通过 {stats['sample_verified']}；"
        f"部分证据 {stats['partial']}；未通过 {stats['open']}。",
        "",
        "## 十关速览", ""
    ]
    for g in d["gates"]:
        lines.append(f"- {g['slug']} {g['title']} [{g['status']}]："
                     f"{g['next_action']}；证据 {', '.join(g['evidence_ids'])}")
    lines += [
        "",
        "## 每轮研究开始与结束时", "",
        "1. 先查询十关清单与相关证据范围，区分 Lean 定理、运行时结果、有限前缀和推测。",
        "2. 选定一个关卡和可证伪的验收标准，保存原始代码版本、真实输入、日志、资源上限。",
        "3. 成功或失败都记录；禁止把超时、样例通过、运行时对比改成内核证明或通用结论。",
        "4. 更新 research/ten_gates.json（唯一可编辑状态源）；运行 --write 重生成看板和 JSONL。",
        "5. 追加 research/REVIEW_LOG.md，记录日期、关卡、证据、已证范围、未解缺口。",
        "6. 运行 --check 再提交；没有新增验收证据时不提升关卡状态。",
        "",
        "这里没有自动运行的向量数据库或后台巡检；GitHub CI 只在被触发时检查资料一致性。",
        ""
    ]
    return "\n".join(lines)


def cards_text(d, evidence):
    lines = []
    for g in d["gates"]:
        sources = [evidence[eid] for eid in g["evidence_ids"]]
        content = "\n".join([
            g["slug"] + " " + g["title"],
            "status=" + g["status"] + " priority=" + g["priority"] + " reviewed=" + g["reviewed_on"],
            "acceptance: " + "；".join(g["acceptance"]),
            "verified: " + ("；".join(g["verified_scope"]) or "无可关闭整关的证据"),
            "blockers: " + ("；".join(g["blockers"]) or "无"),
            "next: " + g["next_action"],
            "evidence: " + "；".join(
                f"{s['id']} {s['claim']} [limit: {s['limit']}] @ {s['path']}"
                for s in sources
            )
        ])
        lines.append(json.dumps({
            "id": g["slug"], "kind": "research_gate", "title": g["title"],
            "status": g["status"], "priority": g["priority"],
            "as_of": d["reviewed_on"], "query_terms": [g["slug"], g["title"]],
            "source_paths": [s["path"] for s in sources],
            "evidence_ids": g["evidence_ids"], "content": content
        }, ensure_ascii=False, sort_keys=True))
    return "\n".join(lines) + "\n"


def search_gates(data, evidence, query, top=3):
    """Local keyword retrieval against the gate cards; no embeddings."""
    needle = query.strip().lower()
    if not needle:
        raise ValueError("Empty search text")
    tokens = [token.lower() for token in re.findall(
        r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[\\u4e00-\\u9fff]{2,}", query
    )]
    matches = []
    for g in data["gates"]:
        title = (g["slug"] + " " + g["title"]).lower()
        haystack = " ".join([
            title, g["next_action"], *g["acceptance"], *g["verified_scope"],
            *g["blockers"], *[evidence[e]["claim"] + " " +
            evidence[e]["limit"] + " " + evidence[e]["path"]
            for e in g["evidence_ids"]]
        ]).lower()
        score = 0
        if needle in title:
            score += 25
        if needle in haystack:
            score += 9
        for token in tokens:
            if token in title:
                score += 9
            if token in haystack:
                score += 2
        if score:
            matches.append((score, g))
    matches.sort(key=lambda pair: (-pair[0], pair[1]["id"]))
    return matches[:top]


def print_search(data, evidence, query, top):
    results = search_gates(data, evidence, query, top)
    print(f"RESEARCH_GATE_LOCAL_RETRIEVAL query={query!r} matches={len(results)}")
    for score, g in results:
        print(f"{g['slug']} [{g['status']}] {g['title']} (score={score})")
        print("  next:", g["next_action"])
        print("  evidence:", ", ".join(evidence[e]["path"] for e in g["evidence_ids"]))
        print("  blockers:", "；".join(g["blockers"]) or "无")


def main():
    p = argparse.ArgumentParser()
    options = p.add_mutually_exclusive_group(required=True)
    options.add_argument("--write", action="store_true")
    options.add_argument("--check", action="store_true")
    options.add_argument("--status", action="store_true")
    options.add_argument("--search", metavar="TEXT", help="Retrieve relevant gates")
    p.add_argument("--top", type=int, default=3)
    args = p.parse_args()
    d = json.loads(REGISTRY.read_text(encoding="utf-8"))
    ev = validate(d)
    if args.search is not None:
        if not 1 <= args.top <= 10:
            p.error("--top must be in [1, 10]")
        print_search(d, ev, args.search, args.top)
        return
    if args.status:
        print(f"snapshot={d['reviewed_on']} upstream={d['original_upstream_commit']}")
        for g in d["gates"]:
            print(f"{g['slug']} [{g['status']}] {g['title']} | next: {g['next_action']}")
        return
    generated = {
        OUTPUTS[0]: board_text(d, ev),
        OUTPUTS[1]: context_text(d),
        OUTPUTS[2]: cards_text(d, ev)
    }
    if args.write:
        for path, text in generated.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
            print("UPDATED", path.relative_to(ROOT))
        return
    mismatches = []
    for path, text in generated.items():
        if not path.is_file() or path.read_text(encoding="utf-8") != text:
            mismatches.append(str(path.relative_to(ROOT)))
    if mismatches:
        raise SystemExit("BOARD_OUT_OF_SYNC: " + ", ".join(mismatches)
                         + " ; run python3 scripts/research_board.py --write")
    print(f"TEN_GATES_BOARD_INTEGRITY_PASS gates=10 evidence={len(ev)} cards=10")


if __name__ == "__main__":
    main()
