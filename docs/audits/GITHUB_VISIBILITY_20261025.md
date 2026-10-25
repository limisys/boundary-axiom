# GitHub 侧可发现性核查（2026-10-25）

**对象：** `limisys/boundary-axiom`
**范围：** 仓库元数据、页面部署状态、站内链接健康、GitHub 仓库搜索命中
**方法：** GitHub REST API 公开端点（repository / search / actions）+ 站点 HTTP 状态探测
**性质：** 只读核查，未修改仓库任何字段

---

## 0. 结论摘要

线上部署与站点健康全部正常；缺口集中在**元数据层**：`topics` 为空、`homepage` 为空，导致仓库在 GitHub 内部检索中几乎不可达。命名层面，`boundary axiom` 已被本仓库独占，但 `boundary cognition` 指向他人仓库，`assembled intelligence` 尚无占位者。

---

## 1. 仓库元数据快照

| 字段 | 值 |
|---|---|
| full_name | limisys/boundary-axiom |
| visibility | public |
| default_branch | main |
| description | Unified Boundary Axiom (统一边界公理) — Lean 4 formalization & versioned research anchor |
| homepage | 未设置 |
| topics | 空 |
| license | Apache-2.0 |
| created_at | 2026-09-08 |
| pushed_at | 2026-10-24T21:26:08Z |
| size | 3272 KB |
| stargazers / forks / watchers | 0 / 0 / 0 |
| open_issues | 0 |
| archived / disabled | false / false |

---

## 2. 页面部署状态

部署方式：GitHub Actions 工作流 `pages`，取 `site/` 目录上传并发布；触发条件为 main 分支 push 或手动触发。最近三次运行结论均为 success。

| URL | 状态 | 大小 | 备注 |
|---|---|---|---|
| `/boundary-axiom/` | 200 | 7,571 B | 入口页，含 og:title / og:image |
| `/boundary-axiom/technical.html` | 200 | 12,754 B | 技术版 |
| `/boundary-axiom/evidence.html` | 200 | 10,945 B | 证据版 |
| `/boundary-axiom/demo.html` | 200 | 39,475 B | 有限状态演示 |
| `/boundary-axiom/open-bridge.html` | 200 | 5,171 B | 开放桥 |
| `/boundary-axiom/bounty.html` | 200 | 5,366 B | 反例征集 |
| `/boundary-axiom/assets/og.png` | 200 | 45,978 B | 社交分享卡，1200×630 |
| 根域 `limisys.github.io` | 200 | 1,923 B | — |
| `caseos.cn` | 200 | 5,839 B | 自建站 |

站点与仓库同域不同源：页面由 main 的 `site/` 构建，与 tag 内容树共享同一 commit 标识。

---

## 3. GitHub 仓库搜索命中

查询口径：GitHub 仓库搜索（名称、描述、topics、README 文本），单位为本仓库是否出现在结果内。

| 检索词 | 命中总数 | 本仓库是否命中 | 首位结果 |
|---|---|---|---|
| `"boundary axiom"` | 1 | 是 | limisys/boundary-axiom |
| `"boundary cognition"` | 1 | 否 | DAMO-NLP-SG/LLM-Multilingual-Knowledge-Boundaries |
| `"boundary programme"` | 1 | 否 | ericrenone/The-Dirac-Boundary-Programme |
| `boundary axiom lean4` | 0 | — | — |
| `"boundary-report"` | 16 | 否 | 多为工程类边界上报工具，与本研究无关 |
| `moore family formalization lean` | 0 | — | — |
| `"assembled intelligence"` | 0 | — | — |

topic 维度：

| topic | 命中总数 | 本仓库是否命中 |
|---|---|---|
| `topic:boundary-axiom` | 0 | 否（该 topic 不存在） |
| `topic:boundary-cognition` | 0 | 否（该 topic 不存在） |
| `topic:formalization` | 296 | 否（因仓库未设 topics） |

解读：

1. `boundary axiom` 作为短语在 GitHub 上只有本仓库一条，命名独占成立；但该短语的检索需求本身接近零，独占不带来流量。
2. 纲领在公开叙事中反复使用的 `boundary cognition`，在 GitHub 侧指向他人仓库。这是唯一一处"名义被占"的位置，需要通过 description / README / topics 明确本仓库为该词的正式载体。
3. `assembled intelligence` 完全空白，是尚未占位的入口。
4. 组合词 `boundary axiom lean4` 零命中，说明 `Lean 4` 的写法与搜索习惯（`lean4`）不一致，且 topics 为空使组合检索无从匹配。

---

## 4. 待改字段与建议值

以下三项需在仓库 Settings 页面手工提交，属于元数据变更，不触及内容树与 tag。

**Description**

```
Boundary cognition research programme (心智有边界) — Lean 4 formalization of boundary–report identity on Moore families, with a finite-state consistency gate and versioned evidence anchors.
```

**Topics**（8 项，均与仓库实际内容对应）

```
lean4
formalization
mathlib
boundary-cognition
research-programme
automated-theorem-proving
self-reference
knowledge-representation
```

**Homepage**

```
https://limisys.github.io/boundary-axiom/
```

预期效果：`topic:lean4`、`topic:boundary-cognition`、`boundary axiom lean4` 三类入口开始对本仓库开放；仓库页出现指向站点的直达链接。

---

## 5. 遗留事项

**gh-pages 分支为旧站镜像。** 该分支最新提交停在 2026-10-20，内容为旧版 `index.html` / `zh.html` / `code/` / `SHA256SUMS` 结构；当前线上站点由 Actions 从 `site/` 部署，不读取该分支。两者并存意味着同一仓库对外存在两套站点版本，且旧版仍可公开访问。处置建议：确认 Actions 部署为唯一来源后删除该分支。删除分支不可逆，需单独授权。

**未提交。** 本文件写入 `docs/audits/`，不自动提交，等待人工检查后由仓库所有者执行 commit。

---

## 6. 复现口径

- 元数据与搜索结果取自 GitHub REST API，查询时刻 2026-10-25（北京时间）。
- 站点状态为 HTTP GET 探测，含 `content-type` 与响应字节数。
- 搜索命中数为 API 返回的 `total_count`，结果受 GitHub 索引更新延迟影响，通常滞后数小时至一天。
- 本核查不涉及账号凭据、不写入任何远端状态。
