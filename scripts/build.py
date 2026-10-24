#!/usr/bin/env python3
"""build.py —— 统一仓 Lean 开发体的离线可复现构建（不依赖 Lake 联网解析）。

做什么
  1. 索引 `lean/*.lean` 与 `vendor/CausModel/**/*.lean` 的本地模块；
  2. 从 `import` 行解析本地依赖，做拓扑分层（同层可并行）；
  3. 用 `lean -o build/<Module>.olean` 逐件编译，Mathlib 只从既有 packages 目录读；
  4. 最后编译单一入口 `BoundaryProgramme`，并检查**每个开发件都从入口可达**；
  5. 写 `data/build_manifest.json`（逐件 sha256／耗时／状态）与失败日志。

用法
  python3 scripts/build.py [--clean] [--jobs N] [--mathlib-packages DIR]

环境
  ELAN_HOME          默认 $HOME/.elan（若 lean 不在 PATH）
  MATHLIB_PACKAGES   可选；默认探测仓库内 .lake/packages 与 CausModel 的 packages

退出码 0 = 全部编译通过、入口覆盖全部开发件；否则 1。
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"
VENDOR_CAUS = ROOT / "vendor" / "CausModel"
BUILD_DIR = LEAN_DIR / "build"
LOG_DIR = ROOT / "logs" / "build"
DATA_DIR = ROOT / "data"
ENTRY = "BoundaryProgramme"

IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)
DEFAULT_ELAN = os.environ.get("ELAN_HOME", str(Path.home() / ".elan"))
PACKAGE_CANDIDATES = [
    str(ROOT / ".lake" / "packages"),
    str(ROOT / "vendor" / "CausModel" / ".lake" / "packages"),
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def discover_modules() -> dict[str, Path]:
    """模块名 → 源文件。主开发体平铺；CausModel 为嵌套包。"""
    mods: dict[str, Path] = {}
    for p in sorted(LEAN_DIR.glob("*.lean")):
        if p.name.startswith("."):
            continue
        mods[p.stem] = p
    if VENDOR_CAUS.is_dir():
        for p in sorted(VENDOR_CAUS.rglob("*.lean")):
            if p.name.startswith("."):
                continue
            rel = p.relative_to(VENDOR_CAUS).with_suffix("")
            mod = ".".join(rel.parts)
            if mod in mods:
                raise SystemExit(f"FAIL 模块名冲突：{mod}（{p}）")
            mods[mod] = p
    if not mods:
        raise SystemExit("FAIL 没有找到任何 .lean 源件")
    return mods


def local_deps(mods: dict[str, Path]) -> dict[str, list[str]]:
    deps = {}
    for mod, p in mods.items():
        code = p.read_text(encoding="utf-8")
        found = []
        for imp in IMPORT_RE.findall(code):
            if imp in mods and imp != mod and imp not in found:
                found.append(imp)
        deps[mod] = found
    return deps


def topo_levels(deps: dict[str, list[str]]) -> list[list[str]]:
    remaining = {m: set(d) for m, d in deps.items()}
    levels: list[list[str]] = []
    done: set[str] = set()
    while remaining:
        ready = sorted(m for m, d in remaining.items() if d <= done)
        if not ready:
            cyc = " → ".join(sorted(remaining)[:8])
            raise SystemExit(f"FAIL 依赖有环或无法解析：{cyc}")
        levels.append(ready)
        for m in ready:
            del remaining[m]
        done.update(ready)
    return levels


def reachable_from(entry: str, deps: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    stack = [entry]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(deps.get(m, []))
    return seen


def resolve_mathlib_packages(arg: str | None) -> Path:
    candidates = []
    if arg:
        candidates.append(arg)
    if os.environ.get("MATHLIB_PACKAGES"):
        candidates.append(os.environ["MATHLIB_PACKAGES"])
    candidates.extend(PACKAGE_CANDIDATES)
    for c in candidates:
        p = Path(c)
        if (p / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean").is_file():
            return p
    raise SystemExit(
        "FAIL 找不到预构建的 Mathlib packages。请用 --mathlib-packages 指定含 "
        "mathlib/.lake/build/lib/lean/Mathlib.olean 的目录。"
    )


def lean_env(mathlib_packages: Path, lean_bin: str) -> dict[str, str]:
    env = os.environ.copy()
    pkg_paths = sorted(
        str(d / ".lake" / "build" / "lib" / "lean")
        for d in mathlib_packages.iterdir()
        if (d / ".lake" / "build" / "lib" / "lean").is_dir()
    )
    env["LEAN_PATH"] = ":".join([str(BUILD_DIR.resolve())] + pkg_paths)
    elan = env.get("ELAN_HOME") or DEFAULT_ELAN
    if Path(elan).is_dir():
        env["ELAN_HOME"] = elan
        env["PATH"] = f"{elan}/bin:" + env.get("PATH", "")
    env["LEAN_BIN"] = lean_bin
    return env


def olean_for(mod: str) -> Path:
    return BUILD_DIR / (mod.replace(".", "/") + ".olean")


def compile_one(mod: str, src: Path, env: dict[str, str], lean_bin: str) -> dict:
    out = olean_for(mod)
    out.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    proc = subprocess.run(
        [lean_bin, "-o", str(out), str(src)],
        cwd=str(ROOT),
        env=env,
        capture_output=True,
        text=True,
    )
    secs = round(time.time() - t0, 2)
    log = (proc.stdout or "") + (proc.stderr or "")
    if log.strip():
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        (LOG_DIR / f"{mod.replace('.', '_')}.log").write_text(log, encoding="utf-8")
    return {
        "module": mod,
        "source": str(src.relative_to(ROOT)),
        "sha256": sha256(src),
        "olean": str(out.relative_to(ROOT)),
        "status": "OK" if proc.returncode == 0 else "FAIL",
        "seconds": secs,
        "log": str((LOG_DIR / f"{mod.replace('.', '_')}.log").relative_to(ROOT))
        if log.strip()
        else None,
        "tail": "\n".join(log.strip().splitlines()[-12:]),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--clean", action="store_true", help="先删除 lean/build 与 logs/build")
    ap.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1))
    ap.add_argument("--mathlib-packages")
    ap.add_argument("--no-caus", action="store_true", help="只构建 lean/，不构建 vendor/CausModel")
    args = ap.parse_args()

    elan = os.environ.get("ELAN_HOME") or DEFAULT_ELAN
    if Path(elan).is_dir():
        os.environ["ELAN_HOME"] = elan
        if shutil.which("lean") is None:
            os.environ["PATH"] = f"{elan}/bin:" + os.environ.get("PATH", "")
    lean_bin = shutil.which("lean")
    if not lean_bin:
        raise SystemExit("FAIL 找不到 lean；请设置 ELAN_HOME 或 PATH。")

    if args.clean:
        shutil.rmtree(BUILD_DIR, ignore_errors=True)
        shutil.rmtree(LOG_DIR, ignore_errors=True)
    BUILD_DIR.mkdir(parents=True, exist_ok=True)
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(exist_ok=True)

    mathlib_packages = resolve_mathlib_packages(args.mathlib_packages)
    mods = discover_modules()
    if args.no_caus:
        mods = {m: p for m, p in mods.items() if not (m == "CausModel" or m.startswith("CausModel."))}
    deps = local_deps(mods)
    levels = topo_levels(deps)
    main_mods = {m for m, p in mods.items() if p.parent == LEAN_DIR}
    missing_entry = ENTRY not in mods
    if missing_entry:
        raise SystemExit(f"FAIL 缺少单一入口 {ENTRY}.lean")

    ver = subprocess.run([lean_bin, "--version"], capture_output=True, text=True, env=os.environ.copy())
    version = (ver.stdout or ver.stderr or "").strip()
    print(f"== lean          : {version}")
    print(f"== mathlib pkgs  : {mathlib_packages}")
    print(f"== modules       : {len(mods)}（主开发体 {len(main_mods)} + CausModel {len(mods)-len(main_mods)}）")
    print(f"== dependency levels: {[len(x) for x in levels]}")
    print(f"== jobs          : {args.jobs}")

    env = lean_env(mathlib_packages, lean_bin)
    results: list[dict] = []
    failed = False
    t0 = time.time()
    for level_no, level in enumerate(levels, 1):
        if failed:
            break
        print(f"-- level {level_no}/{len(levels)}：{len(level)} 件")
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            futs = {pool.submit(compile_one, m, mods[m], env, lean_bin): m for m in level}
            for fut in as_completed(futs):
                r = fut.result()
                results.append(r)
                print(f"   {r['status']:4s} {r['module']:38s} {r['seconds']:6.2f}s")
                if r["status"] != "OK":
                    failed = True
                    print("   ---- 失败尾部 ----")
                    print(r["tail"])

    reached = reachable_from(ENTRY, deps) if not failed else set()
    unreachable = sorted(m for m in main_mods if m not in reached)
    if unreachable and not failed:
        print(f"FAIL 入口不可达的开发件：{', '.join(unreachable)}")
        failed = True

    manifest = {
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "lean_version": version,
        "mathlib_packages": str(mathlib_packages),
        "entry": ENTRY,
        "module_count": len(mods),
        "main_module_count": len(main_mods),
        "levels": [len(x) for x in levels],
        "entry_reachable_modules": len(reached),
        "unreachable_from_entry": unreachable,
        "elapsed_seconds": round(time.time() - t0, 1),
        "status": "OK" if not failed else "FAIL",
        "modules": sorted(results, key=lambda r: r["module"]),
    }
    (DATA_DIR / "build_manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    print(f"== 构建{'通过' if not failed else '失败'}：{sum(r['status']=='OK' for r in results)}"
          f"/{len(mods)} 件，入口覆盖 {len(reached)} 件，用时 {manifest['elapsed_seconds']}s")
    print(f"== manifest: {(DATA_DIR / 'build_manifest.json').relative_to(ROOT)}")
    return 0 if not failed else 1


if __name__ == "__main__":
    sys.exit(main())
