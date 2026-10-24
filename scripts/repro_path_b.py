#!/usr/bin/env python3
"""repro_path_b.py — independent reproduction of paper A results (pure stdlib).

与 path A（论文 §3–§4 的解析推导）相互独立：
  - 本脚本不复用项目 scripts/verify_boundary_theory.py，所有公式从论文定义重写；
  - 数值路径只用于"量值一致"，精确性由 Lean（S4）承担，本脚本在结论中明确标注。
输出：repro_path_b_results.json（工作区内）
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

# ---------- 论文定义（逐条重写，不复用项目脚本） ----------
def sig(z):
    return 1.0 / (1.0 + math.exp(-z))

def hbin(p):
    if p <= 0.0 or p >= 1.0:
        return 0.0
    return -p * math.log(p) - (1.0 - p) * math.log(1.0 - p)

def g(z):
    return hbin(sig(z))

def simpson(f, a, b, n):
    if n % 2:
        n += 1
    h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        s += (4 if i % 2 else 2) * f(a + i * h)
    return s * h / 3.0

# ---------- 1) C_H：两条独立数值路径 ----------
def C_H_integral(L=40.0, n=400000):
    return simpson(g, -L, L, n)

def C_H_series(N=2_000_000):
    # C_H = 2∫_0^1 (-ln x)/(1-x) dx = 2 Σ_{k≥1} 1/k²
    # 部分和 + Euler–Maclaurin 尾项（Σ_{k>N} k^-2 ≈ 1/N - 1/(2N²) + 1/(6N³)）
    s = 0.0
    for k in range(1, N + 1):
        s += 1.0 / (k * k)
    tail = 1.0 / N - 1.0 / (2.0 * N * N) + 1.0 / (6.0 * N ** 3)
    return 2.0 * (s + tail)

exact = math.pi ** 2 / 3.0
c_int = C_H_integral()
c_ser = C_H_series()
r_int = abs(c_int - exact) / exact
r_ser = abs(c_ser - exact) / exact

# ---------- 2) κ* 与均分 ----------
def V(c0, alpha, kappa):
    return c0 * kappa + alpha * math.pi ** 2 / (3.0 * kappa)

def kappa_star(c0, alpha):
    return math.pi * math.sqrt(alpha / (3.0 * c0))

def deriv_fd(f, x, h=1e-6):
    return (f(x + h) - f(x - h)) / (2.0 * h)

random.seed(20261018)
kstar_rows = []
for _ in range(8):
    c0 = 10 ** random.uniform(-2, 2)
    alpha = 10 ** random.uniform(-2, 2)
    ks = kappa_star(c0, alpha)
    dv = deriv_fd(lambda k: V(c0, alpha, k), ks)
    lhs = c0 * ks
    rhs = alpha * math.pi ** 2 / (3.0 * ks)
    kstar_rows.append({
        "c0": c0, "alpha": alpha, "kappa_star": ks,
        "V_prime_at_kstar": dv, "rel_err_V_prime": abs(dv) / (c0 + alpha * math.pi ** 2 / (3 * ks ** 2)),
        "equipartition_lhs": lhs, "equipartition_rhs": rhs,
        "rel_gap_equipartition": abs(lhs - rhs) / max(lhs, rhs),
        "V_star_vs_2c0kstar": abs(V(c0, alpha, ks) - 2 * c0 * ks) / V(c0, alpha, ks),
    })

# ---------- 3) σ*、σ*=1 判据、反平方关系 ----------
sigma_rows = []
for _ in range(8):
    C0 = 10 ** random.uniform(-2, 2)
    alpha = 10 ** random.uniform(-2, 2)
    sig_star_direct = math.pi ** 2 * alpha / (3.0 * C0)
    sigma_rows.append({
        "C0": C0, "alpha": alpha, "sigma_star_formula": sig_star_direct,
        "is_one_iff": (abs(sig_star_direct - 1.0) < 1e-12) == (abs(math.pi ** 2 * alpha - 3 * C0) < 1e-9 * max(1.0, C0)),
    })
# 规范单位：alpha = 3C0/pi^2 ⇒ sigma*=1
C0 = 1.7
alpha_gauge = 3.0 * C0 / math.pi ** 2
sigma_one = math.pi ** 2 * alpha_gauge / (3.0 * C0)

# 反平方：sigma = sigma0 * C_H^2 / H^2，其中 H = C_H/kappa, sigma0 = c0/C0
inv_rows = []
for _ in range(6):
    c0 = 10 ** random.uniform(-2, 2)
    C0 = 10 ** random.uniform(-2, 2)
    for kappa in (0.37, 1.0, 2.9):
        H = exact / kappa
        sigma_from_kappa = (c0 / C0) * kappa ** 2
        sigma_from_H = (c0 / C0) * exact ** 2 / H ** 2
        inv_rows.append({"c0": c0, "C0": C0, "kappa": kappa,
                         "rel_gap_inverse_square": abs(sigma_from_kappa - sigma_from_H) / sigma_from_kappa})

# ---------- 4) 广义力 ----------
force_rows = []
for _ in range(5):
    c0 = 10 ** random.uniform(-2, 2)
    alpha = 10 ** random.uniform(-2, 2)
    for kappa in (0.5, 1.3, 4.0):
        F = alpha * math.pi ** 2 / (3.0 * kappa ** 2) - c0
        Vp = deriv_fd(lambda k: V(c0, alpha, k), kappa, h=1e-7)
        force_rows.append({"c0": c0, "alpha": alpha, "kappa": kappa,
                           "F": F, "minus_V_prime": -Vp, "rel_gap": abs(F + Vp) / max(abs(F), abs(Vp), 1e-300)})

# ---------- 4b) H(κ)=C_H/κ 的直接检验（对 x 积分，不预设换元） ----------
h_scaling = []
for kappa in (0.4, 1.0, 2.5, 6.0):
    mu = 0.3
    L = 40.0 / kappa
    H_num = simpson(lambda x: hbin(sig(kappa * (x - mu))), mu - L, mu + L, 200000)
    H_pred = exact / kappa
    h_scaling.append({"kappa": kappa, "H_numeric": H_num, "H_pred_C_H_over_kappa": H_pred,
                      "rel_gap": abs(H_num - H_pred) / H_pred})


# ---------- 5) 非 sigmoid 场族：C_F ----------
def p_logistic(z): return sig(z)
def p_probit(z):   return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))
def p_tanh(z):     return 0.5 * (1.0 + math.tanh(z))
def p_cauchy(z):   return 0.5 + math.atan(z) / math.pi
def p_heaviside(z): return 1.0 if z > 0 else 0.0

def C_F_of(pfun, L, n):
    return simpson(lambda z: hbin(pfun(z)), -L, L, n)

cf = {
    "logistic":  C_F_of(p_logistic, 40.0, 400000),
    "probit":    C_F_of(p_probit, 40.0, 400000),
    "tanh":      C_F_of(p_tanh, 40.0, 400000),
    "heaviside": C_F_of(p_heaviside, 40.0, 400000),
}

# ---------- 5b) 一般场族定律：κ*=√(αC_F/c₀)、σ*=αC_F/C₀ ----------
general_family = []
for name in ("logistic", "probit", "tanh"):
    cfv = cf[name]
    c0, C0, alpha = 1.3, 0.7, 2.1
    ks = math.sqrt(alpha * cfv / c0)
    sigma_from_kappa = (c0 / C0) * ks ** 2
    sigma_law = alpha * cfv / C0
    general_family.append({"F": name, "C_F": cfv, "kappa_star": ks,
                           "sigma_star_from_kappa": sigma_from_kappa,
                           "sigma_star_law_alphaC_F_over_C0": sigma_law,
                           "rel_gap": abs(sigma_from_kappa - sigma_law) / sigma_law})

# Cauchy：1-p(z) ~ 1/(πz) ⇒ h(p) ~ ln(πz)/(πz) ⇒ C_F(L) ~ (ln L)^2/2（对数平方发散，非线性）
cauchy_curve = {str(L): C_F_of(p_cauchy, float(L), 200000) for L in (40, 80, 160, 320)}
Ls = [40.0, 80.0, 160.0, 320.0]
ys = [cauchy_curve[str(int(L))] for L in Ls]
# 拟合 C_F(L) = a*(ln L)^2 + b，用 L=80,320 定点，检验 L=40,160 的残差
a_fit = (ys[3] - ys[1]) / ((math.log(Ls[3]) ** 2) - (math.log(Ls[1]) ** 2))
b_fit = ys[1] - a_fit * math.log(Ls[1]) ** 2
log2_residual = {int(L): abs(a_fit * math.log(L) ** 2 + b_fit - y) / y
                 for L, y in zip(Ls, ys)}
cauchy_increments = [ys[i + 1] - ys[i] for i in range(3)]

# 重尾族 p(z)=1-(1+z)^-a（z≥0，双侧对称）：a=1 发散、a=1.5 收敛
def C_F_heavy_tail(a, L, n=200000):
    f = lambda z: hbin(1.0 - (1.0 + z) ** (-a)) if z >= 0 else hbin((1.0 + (-z + 1.0)) ** (-a)) * 0 + hbin(1.0 - (1.0 - z) ** (-a)) if z < 0 else 0.0
    # 明确写法：p(z)=1-(1+|z|)^-a
    f = lambda z: hbin(1.0 - (1.0 + abs(z)) ** (-a))
    return simpson(f, -L, L, n)

heavy = {
    "a=1.0":  {str(L): C_F_heavy_tail(1.0, float(L)) for L in (40, 80, 160, 320)},
    "a=1.5":  {str(L): C_F_heavy_tail(1.5, float(L)) for L in (40, 80, 160, 320)},
}

# 关键反例族：1-p ~ 1/(z (ln z)^2)。它"快于 1/(z ln z)"（论文所称有效域），
# 但 h(p) ~ 1/(z ln z)，故 C_F ~ ln ln L 仍发散。用于检验论文有效域判据是否充分。
def C_F_log_over_z(L, n=200000):
    f = lambda z: hbin(1.0 - 0.5 / ((1.0 + abs(z)) * (math.log(2.0 + abs(z)) ** 2)))
    return simpson(f, -L, L, n)

logoz = {str(L): C_F_log_over_z(float(L)) for L in (40, 80, 160, 320)}
_ll = {L: math.log(math.log(L)) for L in (40.0, 80.0, 160.0, 320.0)}
_a2 = (logoz["320"] - logoz["80"]) / (_ll[320.0] - _ll[80.0])
_b2 = logoz["80"] - _a2 * _ll[80.0]
logoz_residual = {int(L): abs(_a2 * _ll[L] + _b2 - logoz[str(int(L))]) / logoz[str(int(L))]
                  for L in (40.0, 80.0, 160.0, 320.0)}

# ---------- 6) 组装递推吸引子 ----------
eta, D = 0.3, 2.0
sigma_n = 0.5
for _ in range(200):
    sigma_n = sigma_n / (1.0 + eta) + D
sigma_inf_formula = D * (1.0 + 1.0 / eta)
assemb = {"eta": eta, "D": D, "sigma_iterate_200": sigma_n,
          "sigma_inf_formula": sigma_inf_formula,
          "rel_gap": abs(sigma_n - sigma_inf_formula) / sigma_inf_formula}

# ---------- 6b) Noether 能量守恒：ODE 数值积分（RK4），E=½Iκ̇²+V(κ) ----------
def noether_drift(c0=1.0, alpha=1.0, I=1.0, k0=2.0, kd0=0.0, dt=1e-3, T=10.0):
    def acc(k):
        return (alpha * math.pi ** 2 / (3.0 * k * k) - c0) / I
    def E(k, kd):
        return 0.5 * I * kd * kd + V(c0, alpha, k)
    def rhs(k, kd):
        return kd, acc(k)
    k, kd = k0, kd0
    E0 = E(k, kd)
    worst = 0.0
    steps = int(T / dt)
    for _ in range(steps):
        a1, b1 = rhs(k, kd)
        a2, b2 = rhs(k + 0.5 * dt * a1, kd + 0.5 * dt * b1)
        a3, b3 = rhs(k + 0.5 * dt * a2, kd + 0.5 * dt * b2)
        a4, b4 = rhs(k + dt * a3, kd + dt * b3)
        k = k + dt / 6.0 * (a1 + 2 * a2 + 2 * a3 + a4)
        kd = kd + dt / 6.0 * (b1 + 2 * b2 + 2 * b3 + b4)
        worst = max(worst, abs(E(k, kd) - E0) / E0)
    return {"E0": E0, "max_rel_drift": worst, "steps": steps, "dt": dt, "T": T}

noether = noether_drift()

# ---------- 6c) Landau 双阱：V(φ;r) = -rφ² + φ⁴ 的临界点与稳定性 ----------
def landau_roots(r):
    # V(φ;r) = -rφ² + φ⁴；V'(φ) = -2rφ + 4φ³ = 2φ(2φ² - r)；V''(φ) = -2r + 12φ²
    if r <= 0:
        return {"phi": [0.0], "Vpp": [-2 * r], "stable": [-2 * r > 0]}
    p = math.sqrt(r / 2.0)
    vpp_out = -2 * r
    vpp_well = -2 * r + 12 * p * p
    return {"phi": [0.0, p, -p], "Vpp": [vpp_out, vpp_well, vpp_well],
            "stable": [vpp_out > 0, vpp_well > 0, vpp_well > 0]}
landau = {str(r): landau_roots(r) for r in (0.5, 0.0, -0.5)}

# ---------- 汇总 ----------
tol_int = 1e-9
checks = {
    "C_H_integral_vs_exact":   {"value": c_int, "rel_err": r_int, "pass": r_int < tol_int},
    "C_H_series_vs_exact":     {"value": c_ser, "rel_err": r_ser, "pass": r_ser < tol_int},
    "kappa_star":              {"max_rel_err_V_prime": max(r["rel_err_V_prime"] for r in kstar_rows),
                                "max_rel_gap_equipartition": max(r["rel_gap_equipartition"] for r in kstar_rows),
                                "max_rel_gap_V_star": max(r["V_star_vs_2c0kstar"] for r in kstar_rows)},
    "sigma_star":              {"gauge_value": sigma_one, "gauge_is_one": abs(sigma_one - 1.0) < 1e-12,
                                "iff_all_true": all(r["is_one_iff"] for r in sigma_rows)},
    "inverse_square":          {"max_rel_gap": max(r["rel_gap_inverse_square"] for r in inv_rows)},
    "force_equals_minus_grad": {"max_rel_gap": max(r["rel_gap"] for r in force_rows)},
    "C_F_families":            cf,
    "H_scaling_direct":        {"rows": h_scaling, "max_rel_gap": max(r["rel_gap"] for r in h_scaling)},
    "general_family_law":      {"rows": general_family, "max_rel_gap": max(r["rel_gap"] for r in general_family)},
    "cauchy_curve":            cauchy_curve,
    "cauchy_log_squared_fit":  {"a_fit": a_fit, "b_fit": b_fit, "rel_residual": log2_residual,
                                "increments": cauchy_increments},
    "heavy_tail_family":       heavy,
    "log_over_z_counterexample": {"curve": logoz, "A": _a2, "B": _b2, "rel_residual": logoz_residual},
    "assembly_attractor":      assemb,
    "noether_energy_drift":    noether,
    "landau_bifurcation":      landau,
}
checks["kappa_star"]["pass"] = (checks["kappa_star"]["max_rel_err_V_prime"] < 1e-6 and
                                checks["kappa_star"]["max_rel_gap_equipartition"] < 1e-12 and
                                checks["kappa_star"]["max_rel_gap_V_star"] < 1e-9)
checks["inverse_square"]["pass"] = checks["inverse_square"]["max_rel_gap"] < 1e-12
checks["H_scaling_direct"]["pass"] = checks["H_scaling_direct"]["max_rel_gap"] < 1e-6
checks["general_family_law"]["pass"] = checks["general_family_law"]["max_rel_gap"] < 1e-12
checks["force_equals_minus_grad"]["pass"] = checks["force_equals_minus_grad"]["max_rel_gap"] < 1e-6
checks["C_F_families"]["pass"] = (abs(cf["logistic"] - math.pi ** 2 / 3) / (math.pi ** 2 / 3) < 1e-9
                                  and abs(cf["tanh"] - math.pi ** 2 / 6) / (math.pi ** 2 / 6) < 1e-9
                                  and abs(cf["probit"] - 1.8064) < 5e-4
                                  and cf["heaviside"] == 0.0)
# Cauchy：判定"发散"，并用 (ln L)^2 拟合（残差 <2%）确认发散速率
checks["cauchy_diverges_as_log_squared"] = {
    "monotone_growth": cauchy_increments[0] < cauchy_increments[1] < cauchy_increments[2],
    "max_rel_residual_log2_fit": max(log2_residual.values()),
    "pass": (cauchy_increments[0] < cauchy_increments[1] < cauchy_increments[2]
             and max(log2_residual.values()) < 0.02),
}
# 重尾族：a=1 发散；a=1.5 收敛（阈值是 a=1，即 1-p=o(1/z)）
# a=1.5 的收敛用解析尾余量检验：C_F(L) + 2*∫_{L+1}^∞ u^-a(1+a ln u) du ≈ 常数
def tail_remainder(a, L):
    U = L + 1.0
    return U ** (1 - a) * (1.0 / (a - 1) + a * math.log(U) / (a - 1) + a / (a - 1) ** 2)

h1 = heavy["a=1.0"]; h15 = heavy["a=1.5"]
i1 = [h1["80"] - h1["40"], h1["160"] - h1["80"], h1["320"] - h1["160"]]
conv_limits = {int(L): h15[str(int(L))] + 2 * tail_remainder(1.5, float(L)) for L in (40, 80, 160, 320)}
conv_spread = (max(conv_limits.values()) - min(conv_limits.values())) / max(conv_limits.values())
checks["heavy_tail_threshold_a_equals_1"] = {
    "a1_curve": h1,
    "a1_diverges": (h1["320"] - h1["160"]) > 0.5,
    "a15_converged_limits": conv_limits,
    "a15_limit_spread_rel": conv_spread,
    "pass": ((h1["320"] - h1["160"]) > 0.5 and conv_spread < 0.02),
}
# 论文判据不充分的反例：比 1/(z ln z) 更快的尾，C_F 仍发散（~ln ln L）
lg_inc = [logoz["80"] - logoz["40"], logoz["160"] - logoz["80"], logoz["320"] - logoz["160"]]
checks["domain_criterion_insufficient"] = {
    "curve": logoz,
    "increments": lg_inc,
    "max_rel_residual_loglog_fit": max(logoz_residual.values()),
    "grows_without_bound": {int(L): logoz[str(int(L))] for L in (40, 80, 160, 320)},
    "pass": (max(logoz_residual.values()) < 0.02 and _a2 > 0
             and logoz["320"] > 1.1 * logoz["40"]),
}
checks["assembly_attractor"]["pass"] = assemb["rel_gap"] < 1e-9

out = {
    "script": "scripts/repro_path_b.py",
    "script_sha256": hashlib.sha256(open(__file__, "rb").read()).hexdigest(),
    "python": platform.python_version(),
    "env": platform.platform(),
    "elapsed_s": round(time.time() - T0, 2),
    "exact_pi2_over_3": exact,
    "checks": checks,
    "rows": {"kappa_star": kstar_rows, "sigma_star": sigma_rows,
             "inverse_square": inv_rows, "force": force_rows},
    "note": "数值路径只能给出量值一致（≤1e-9 相对误差），不能证明精确恒等式；精确性由 S4 的 Lean 定理承担。",
}
_fail = [k for k, v in checks.items() if isinstance(v, dict) and v.get("pass") is False]
if _fail:
    print("FAIL", _fail)
    sys.exit(1)

json.dump(out, open(_OUT / "repro_path_b_results.json", "w", encoding="utf-8"), ensure_ascii=False, indent=2)

print(json.dumps({k: (v.get("pass") if isinstance(v, dict) and "pass" in v else "info") for k, v in checks.items()},
                 ensure_ascii=False, indent=2))
print("C_H(integral) =", c_int, " rel_err =", r_int)
print("C_H(series)   =", c_ser, " rel_err =", r_ser)
print("C_F:", {k: round(v, 6) for k, v in cf.items()})
print("cauchy:", cauchy_curve, "log2 rel_residual:", {k: round(v,4) for k,v in log2_residual.items()})
print("heavy a=1:", heavy["a=1.0"], "\nheavy a=1.5:", heavy["a=1.5"])

print("elapsed", round(time.time() - T0, 2), "s")
