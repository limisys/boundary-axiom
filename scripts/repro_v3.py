#!/usr/bin/env python3
"""repro_v3.py — independent numerical check of the nine-component spine (paper B).

与 path A（evidence/S3_path_a_derivation_v3.md 的解析推导）独立：
本脚本从 docs/56 的定义重写，不复用 lean_check 下任何脚本；纯标准库。
输出：repro_v3_results.json
"""
import argparse
import json
import sys, math, random, hashlib, platform, time


_ap = argparse.ArgumentParser()
_ap.add_argument("--data-dir", default="data")
_args = _ap.parse_args()
from pathlib import Path as _Path
_OUT = _Path(_args.data_dir); _OUT.mkdir(parents=True, exist_ok=True)

T0 = time.time()

def sig(z): return 1.0 / (1.0 + math.exp(-z))
def b(kappa, mu, x): return 1.0 - abs(2.0 * sig(kappa * (x - mu)) - 1.0)
def L(theta): return math.log((2.0 - theta) / theta)
def thetaOf(w): return 2.0 / (1.0 + math.exp(w))
def relax(w): return (w + 1.0 / w) / 2.0

def close(a, b_, tol=1e-12): return abs(a - b_) <= tol * max(1.0, abs(a), abs(b_))

checks = {}

# 1) θ* = 2/(1+e)，L(θ(w))=w
theta_star = thetaOf(1.0)
checks["theta_star"] = {"value": theta_star, "expected_2_over_1pe": 2.0 / (1.0 + math.e),
                        "L_roundtrip": L(theta_star), "pass": close(L(theta_star), 1.0) and close(theta_star, 2.0/(1.0+math.e))}
rt = [(w, abs(L(thetaOf(w)) - w)) for w in (0.25, 0.5, 1.0, 2.0, 5.0)]
checks["L_theta_roundtrip"] = {"rows": rt, "max_err": max(e for _, e in rt), "pass": max(e for _, e in rt) < 1e-12}

# 2) 接缝定理：Fix(c_{κ,μ,w}) = {x : b(x) ≤ θ(w)}，网格扫描
def fix_membership(k, mu, w, x):
    # c: 带内 [μ-w/κ, μ+w/κ] 映到 μ+w/κ，带外恒等
    lo, hi = mu - w / k, mu + w / k
    return x <= lo + 1e-12 or x >= hi - 1e-12  # Fix = (-∞,lo] ∪ [hi,∞)
def seam_check(k, mu, w, n=4000, span=4.0):
    xs = [mu - span + 2 * span * i / n for i in range(n + 1)]
    mism = 0
    for x in xs:
        lhs = fix_membership(k, mu, w, x)
        rhs = b(k, mu, x) <= thetaOf(w) + 1e-12
        if lhs != rhs: mism += 1
    return mism
seam_rows = []
for k, mu, w in ((1.0, 0.0, 1.0), (2.0, 0.3, 0.7), (0.5, -1.0, 2.0), (3.0, 1.2, 0.4)):
    seam_rows.append({"kappa": k, "mu": mu, "w": w, "mismatches": seam_check(k, mu, w)})
checks["seam_theorem"] = {"rows": seam_rows, "max_mismatch": max(r["mismatches"] for r in seam_rows),
                          "pass": max(r["mismatches"] for r in seam_rows) == 0}

# 3) 读出：readout(κ,μ,w) = b(μ+w/κ) = θ(w)
read_rows = []
for k, mu, w in ((1.0, 0.0, 0.5), (2.5, -0.4, 1.3), (0.7, 2.0, 3.1)):
    read_rows.append({"kappa": k, "mu": mu, "w": w,
                      "readout": b(k, mu, mu + w / k), "theta": thetaOf(w),
                      "err": abs(b(k, mu, mu + w / k) - thetaOf(w))})
checks["readout_eq_theta"] = {"rows": read_rows, "max_err": max(r["err"] for r in read_rows),
                              "pass": max(r["err"] for r in read_rows) < 1e-14}

# 4) 夹逼：relax 迭代单调降到 1，θ 升到 θ*，永不越过；任意更低水平有限步被超过
def relax_n(w0, n):
    w = w0
    for _ in range(n): w = relax(w)
    return w
sq_rows = []
for w0 in (1.5, 3.0, 10.0):
    w = w0; th = [thetaOf(w)]
    for _ in range(200):
        w = relax(w); th.append(thetaOf(w))
    sq_rows.append({"w0": w0, "w_200": w, "max_theta": max(th), "theta_star": theta_star,
                    "never_exceeds": max(th) <= theta_star + 1e-15,
                    "monotone": all(th[i] <= th[i+1] + 1e-15 for i in range(len(th)-1)),
                    "halving_bound": all((relax_n(w0, n) - 1) <= (w0 - 1) / 2 ** n + 1e-12 for n in range(0, 40))})
checks["squeeze"] = {"rows": sq_rows, "pass": all(r["never_exceeds"] and r["monotone"] for r in sq_rows)}
# 任意更低水平 θ' 有限步被超过
w = 10.0; hit = {}
for thp in (0.5, 0.53, 0.537):
    w = 10.0
    n = 0
    while thetaOf(w) <= thp and n < 10**6:
        w = relax(w); n += 1
    hit[str(thp)] = n
checks["climb"] = {"steps_to_exceed": hit, "pass": all(v < 10**6 for v in hit.values())}

# 5) 两点证伪：两个不同距离读数相同 ⇒ 校准恒等式不成立
phi_flat = lambda d: thetaOf(1.0)          # 常数核：在任意两点上相同
d1, d2 = 0.7, 2.3
checks["two_point_falsifier"] = {
    "phi_d1": phi_flat(d1), "phi_d2": phi_flat(d2),
    "L_phi_d1": L(phi_flat(d1)), "L_phi_d2": L(phi_flat(d2)),
    "distances_distinct": d1 != d2, "violates_calibration": abs(L(phi_flat(d1)) - d1) > 1e-9,
    "pass": (abs(phi_flat(d1) - phi_flat(d2)) < 1e-15 and abs(L(phi_flat(d1)) - d1) > 1e-9)}

# 6) 值层极小：V(κ)=c0κ+αC_F/κ，κ*=√(αC_F/c0)
random.seed(20261018)
v_rows = []
CF = math.pi ** 2 / 3
for _ in range(8):
    c0 = 10 ** random.uniform(-2, 2); alpha = 10 ** random.uniform(-2, 2)
    ks = math.sqrt(alpha * CF / c0)
    f = lambda k: c0 * k + alpha * CF / k
    # 黄金分割极小
    lo, hi = ks / 10.0, ks * 10.0
    gr = (math.sqrt(5) - 1) / 2
    for _ in range(200):
        a = hi - gr * (hi - lo); bb = lo + gr * (hi - lo)
        if f(a) < f(bb): hi = bb
        else: lo = a
    kn = (lo + hi) / 2
    v_rows.append({"c0": c0, "alpha": alpha, "kappa_star": ks, "kappa_numeric": kn,
                   "rel_err": abs(kn - ks) / ks,
                   "scale_invariant": abs(math.sqrt((2*alpha) * CF / (2*c0)) - ks) < 1e-12 * ks})
checks["value_min"] = {"rows": v_rows, "max_rel_err": max(r["rel_err"] for r in v_rows),
                       "pass": max(r["rel_err"] for r in v_rows) < 1e-6 and all(r["scale_invariant"] for r in v_rows)}

# 6b) 校准恒等式 L(b(μ+d/κ))=d
cal_rows = []
for k, mu in ((2.5, -0.4), (0.8, 1.0)):
    for d in (0.3, 1.0, 2.0, 3.0):
        cal_rows.append({"kappa": k, "d": d, "L_b": L(b(k, mu, mu + d / k)), "err": abs(L(b(k, mu, mu + d / k)) - d)})
checks["calibration_identity"] = {"rows": cal_rows, "max_err": max(r["err"] for r in cal_rows),
                                  "pass": max(r["err"] for r in cal_rows) < 1e-12}

# 6c) C06 的轨道采样：规范不变的 P 在轨道 {tw} 上恒定（恒真/恒假）；能挑出唯一 w 的 P 必不恒定
def inv_across_orbit(P, w, ts=(0.5, 1.0, 1.7, 3.0)):
    return len({P(t * w) for t in ts}) == 1
orbit = {"P_w_positive": [inv_across_orbit(lambda w: w > 0, w) for w in (0.3, 1.0, 2.0)],
         "P_w_below_1": [inv_across_orbit(lambda w: w < 1, w) for w in (0.3, 1.0, 2.0)],
         "P_w_equals_1": [inv_across_orbit(lambda w: abs(w - 1) < 1e-12, w) for w in (0.3, 1.0, 2.0)]}
checks["orbit_sampling_C06"] = {"orbit": orbit,
    "pass": all(orbit["P_w_positive"]) and not all(orbit["P_w_below_1"]) and not all(orbit["P_w_equals_1"])}

# 6d) C08：不同水平给出不同已决集（对称差非空）
def decided(k, mu, th, x): return b(k, mu, x) <= th
k, mu = 1.3, 0.2
t1, t2 = 0.4, 0.6
diff = [x for x in [mu - 4 + 8 * i / 2000 for i in range(2001)] if decided(k, mu, t1, x) != decided(k, mu, t2, x)]
checks["level_separation_C08"] = {"theta1": t1, "theta2": t2, "symmetric_difference_points": len(diff),
    "pass": len(diff) > 0}

# 7) 半衰期：ρ(t)=2^{-t}，半衰期恰为 1
rho = lambda t: 2.0 ** (-t)
hl = [rho(1.0), rho(2.0), rho(3.0)]
checks["half_life"] = {"rho1": hl[0], "rho2": hl[1], "ratio": hl[1] / hl[0],
                       "pass": abs(hl[0] - 0.5) < 1e-15 and abs(hl[1] / hl[0] - 0.5) < 1e-15}

out = {"script": "scripts/repro_v3.py",
       "script_sha256": hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
       "python": platform.python_version(), "env": platform.platform(),
       "elapsed_s": round(time.time() - T0, 2),
       "theta_star": theta_star, "checks": checks,
       "note": "数值一致只给量值/结构核对；精确性由 Lean（S4）承担。接缝的 Fix 成员判定按论文 c 的分段定义手写，未调用 Lean。"}
_fail = [k for k, v in checks.items() if isinstance(v, dict) and v.get("pass") is False]
if _fail:
    print("FAIL", _fail)
    sys.exit(1)

json.dump(out, open(_OUT / "repro_v3_results.json", "w", encoding="utf-8"), ensure_ascii=False, indent=2)
print(json.dumps({k: {kk: vv for kk, vv in v.items() if kk in ('pass','max_err','max_mismatch','max_rel_err','value')} for k, v in checks.items()}, ensure_ascii=False, indent=1))
print("theta* =", theta_star)
