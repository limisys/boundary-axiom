# 邻近文献核查（2026Q4，采样版）

# 0. 结论摘要

1. **窗口内无同名研究。** 四组同名/近名检索（`"boundary cognition"`、`"cognitive boundary" AND hypothesis`、`"mind has a boundary"`、`"assembled intelligence"`）在 2026-09-05 至 2026-10-26 窗口内命中为 **0**。唯一全时段同名近似命中为 arXiv:2504.13816（2025-04-18，cs.CL），题名 "Analyzing LLMs' Knowledge Boundary Cognition Across Languages"，其 "boundary cognition" 指 **LLM 对自身知识边界的识别能力**，属工程侧 knowledge boundary 研究，与 boundary-axiom 的"认知主体边界"命题不是同一对象。**术语空位仍然成立。**
2. **邻近带高度拥挤。** 交叉采样去重后 674 篇（窗口内），主题命中：评测/基准 412、认知/心智理论 274、神经科学/脑 270、agent/自主性 247、规模/涌现 143、**边界/限制 65**、法律/规范 33、主观体验 4。换言之，**"边界"一词在工程文献中已被大量占用，但占据的是能力边界与安全边界，而非认知主体的结构性边界。**
3. **对本纲领的直接后果：** 差异化定位必须压在"**可计算、可测试**"这一层，而不是"边界"这一词面。当前 arXiv 潮流把边界处理为 **评测分数**（能不能/准不准）或 **运行时约束**（允许不允许），缺少把边界处理为 **结构判据**（在什么条件下主体必然失配）的工作。这是本纲领的插入点，也是最容易被误读为"又一篇 benchmark"的位置。
4. **风险提示：** x2/x3/x5 三组查询均触达 API 单次 200 条上限（按提交时间倒序），故"674 篇"是**采样**而非全量；真实窗口内 cs.AI/cs.LG 认知类文献量级远大于此。本报告的定量占比只能作趋势判读，不能作穷尽性统计。

---

# 1. 检索方法

| 项 | 内容 |
|---|---|
| 出口 | i7 直连 export.arxiv.org（HTTP 200，隧道白名单第 43 行含 arxiv.org / export.arxiv.org，实际未走隧道） |
| 接口 | arXiv Atom API，`sortBy=submittedDate&sortOrder=descending` |
| 窗口 | 2026-09-05 至 2026-10-26（50 天） |
| 脚本 | `~/arxiv_scan.py`（采集）、`~/analyze.py`（去重与主题命中）、`~/clist.py`（候选抽取） |
| 产物目录 | `~/workspace/research/boundary_scan_20261025/`（i7 本地） |
| 去重键 | arXiv id 去版本号 |

九组查询：

| tag | 查询式 | 取回 | 窗口内保留 | 备注 |
|---|---|---|---|---|
| name_a | `all:"boundary cognition"` | 1 | 1（窗口外） | 全时段仅 1 条，2025-04 |
| name_b | `all:"cognitive boundary" AND all:hypothesis` | 0 | 0 | 无 |
| name_c | `all:"mind has a boundary"` | 0 | 0 | 无 |
| name_d | `all:"assembled intelligence"` | 0 | 0 | 无 |
| x1 | `cat:cs.AI AND (neuroscience / neural mechanism / brain)` | 200 | 129 | 日期跨 2026-08-10 起 |
| x2 | `cat:cs.AI AND (cognitive / cognition)` | 200 | 200 | **触顶** |
| x3 | `cat:cs.LG AND (brain / cognitive / neuroscience)` | 200 | 200 | **触顶** |
| x4 | `cat:q-bio.NC AND (language model / AI / ML)` | 40 | 40 | 未触顶，q-bio.NC 本身稀疏 |
| x5 | `cat:cs.AI AND abs:agent AND (autonomy / autonomous)` | 200 | 200 | **触顶** |

取样窗口分布：x2 覆盖 2026-09-11 → 10-22；x3 同；x5 覆盖 2026-09-29 → 10-22（说明近一个月 agent 自主性文献单日投放量极大）；x1 覆盖 2026-08-10 → 10-22。

---

# 2. 邻近带一：知识边界与能力边界（工程侧，最易混淆带）

这是"boundary"一词在 arXiv 上的**主占用区**：把模型的知识/能力边界当作可探测对象。代表进展是"用内部表征判定已知/未知"，以及把边界认知迁移到多语言。

- **2504.13816** (2025-04-18, cs.CL) Analyzing LLMs' Knowledge Boundary Cognition Across Languages Through the Lens of Internal Representations — 用内部表征探测多语言下的已知/未知边界。**与本纲领词面最近、命题最远的一篇，必须在 PRIOR_ART 中显式区隔，否则评审会默认归入此带。**
- **2609.34864** (2026-09-28) On the Limits of Metacognitive Monitoring in LLMs — 直接处理自我监测的界限，属"元认知边界"，与本纲领的"自我模型边界"可对话。
- **2609.35409** (2026-09-28) AwarenessBench: Assessing Cognitive Capabilities of Language Models — 把"认知能力"操作化为基准，是本纲领最需要避免被同类化的范式样板。
- **2610.04168** (2026-10-03) Agentic Cognitive Depth: Operational Criteria for Evaluating LLM Agents — "operational criteria" 是本纲领可借用的表述资源：把哲学命题转成可操作判据。
- **2610.30945** (2026-10-22) Metacognitive Scaffolds Create Productive Friction for AI-Assisted Knowledge Work — "生产性摩擦" 可作为边界不可消除性的经验旁证。

**判读：** 此带把边界等同于"模型对其能力范围的无知程度"，度量单位是准确率。本纲领若也谈边界，必须说明度量的不是**知道多少**，而是**在何种结构条件下主体必然无法自洽**。这是两条不同的问题线。

---

# 3. 邻近带二：元认知、自我建模与社会认知

- **2609.17331** (2026-09-15) Self-Emergence Agent Architecture: Behavior-Inertia HMM, Reflexive Metacognition, and Social-Contrastive Self-Modeling — 反身元认知 + 自我建模，架构层最接近"自我模型有边界"的工程实现。
- **2610.31060** (2026-10-22) Diagnosing the Explicit-to-Applied Theory of Mind Gap in LLMs — **显式能力与应用能力之间存在落差**。这是本纲领可以引用的强经验证据：能说对 ≠ 能做对，落差不因规模消失。
- **2610.17310** (2026-10-12) Beyond Successful Play: Diagnosing Opponent Modeling in LLMs — 同上结构，在博弈域复现。
- **2609.23722 → 2610.23722** (2026-10-16) Beyond Large Language Models: A Mental World Model Framework for Mental Modeling, Simulation, Evolution, and Interpretability — 心智世界模型框架。
- **2610.28539** (2026-10-20) Humans Correct Their Judgments Through Debate, but Weaker AI Models Do Not — **弱模型无法通过辩论自我修正**，即自我修正能力本身有边界，且与能力水平相关。
- **2609.16245** (2026-09-14) Metacognitive Steering: Learning the Structure of Scientific Judgment — 元认知可被结构化并引导。

**判读：** 这一带正在自发地发现"能力—应用落差"与"自我修正失效"现象，但普遍处理为**待修复的工程缺陷**。本纲领的差异在于：把这类落差读作**边界的显影**，而非缺陷。

---

# 4. 邻近带三：agent 自主性边界与运行时保障（增长最快）

近 50 天最密集的动向：不再讨论 agent 能做什么，而是讨论**如何给 agent 划活动范围并强制遵守**。这是"边界"在工程语境中的第二种占用方式。

- **2610.31376** (2026-10-22) Certified Execution Harness for Agentic AI: Safe and Least-Intrusive Petri-Net Supervisory Control — Petri 网监督控制，在推理与执行之间设卡。
- **2609.39717** (2026-09-30) Trust Is Not a Score: Runtime Assurance Contracts for High-Risk AI Agents — 明确反对把信任化约为评分，主张运行时契约。**与本纲领"边界不可化约为单一指标"的立场同向，可作盟友引用。**
- **2610.30445** (2026-10-21) A Three-Pillar Governance Framework for Safe and Trustworthy AI Agents — 治理三支柱。
- **2610.24277** (2026-10-16) SPIDES: Information-Flow Control for Browser Agents — 信息流控制即边界控制。
- **2610.30557** (2026-10-22) Governed Self-Evolution for Autonomous Investing: Multi-Agent LLM with an Invariant Core — **不变量内核**：自我演化但核心不可变，是"边界作为不变约束"的工程原型。
- **2609.24944 → 2610.24944** (2026-10-18) Epi: Towards a Persistent, Self-Improving Agent for Autonomous Research — 持续自我改进 agent，边界问题被推迟而非解决。
- **2610.09264** (2026-10-07) Package Hallucination Attacks on Coding Agents through Prompt Injection in Rule Files；**2610.08662** (2026-10-06) ParanoiaEval: Benchmarking Unnecessary Defensive Work in Agentic Coding — 后者尤其有价值：**过度防御**是边界设定失当的对称失效，说明边界既可过宽也可过窄。

**判读：** 此带把边界理解为**外部施加的约束**（沙箱、契约、监督器）。本纲领如果把边界理解为**内生的结构性限制**，必须与此带显式区分，否则会被读成又一种 guardrail 方案。2610.30557 的 "invariant core" 与 2610.08662 的 "过度防御" 是两个最佳对话点。

---

# 5. 邻近带四：神经科学与 AI 的再交叉（疫情后回暖的实证痕迹）

- **2609.25146** (2026-09-21) Brain-Inspired Hierarchical Modularity for General Continual Learning — 层级模块化对应持续学习，是"结构约束换泛化"的典型。
- **2609.24324** (2026-09-21) Brain-Token Learning: Microstate-Based Tokenization for Long-Horizon EEG；**2610.20349** (2026-10-14) NeuroDETR: Multiscale Discrete Spatiotemporal Tokenization for EEG；**2610.03001** (2026-10-02) Neural Data Needs Semantic Tokenization — **神经数据正在被 token 化**，这是本轮交叉最鲜明的技术动向：把脑信号并入语言模型的表示范式。
- **2610.29720** (2026-10-21) Bio-Inspired Auditory Processing: Parallel Resonate-and-Fire + Ternary Recurrent Networks；**2610.16273** (2026-10-12) Deep Speech Representations Track Word Timing along a Low-Dimensional Circular Trajectory — 低维几何结构承载时间信息，"低维流形"可作为边界的形式化载体。
- **2609.09306** (2026-09-08) Differential Functionalism: Jacobians Shape the Structure of Phenomenal Experience — 用雅可比结构刻画主观体验的结构，是目前最接近"从动力学结构推出体验结构"的形式化尝试；**若本纲领需要一条"结构决定可及范围"的技术支点，这是首选。**（注意：本文属哲学—形式化交叉，非实证神经科学。）
- **2606.11245** (2026-06-05，窗口外但在引用半径内) Position: Hippocampal Explicit Memory Is the Cornerstone for AGI — 显式记忆作为 AGI 基石，可支撑"记忆结构限定可及范围"的论证。

**判读：** 疫情后神经科学×计算机科学的交叉已从"借喻"（brain-inspired）转向"**数据与表示层的实质合并**"（EEG tokenization、低维流形）。本纲领若停留在隐喻层（心智像什么），会被这一波实证工作挤出。必须给出可算的量。

---

# 6. 对 14 条关键引用的挂接建议

不新增引用条目，仅在既有 14 条骨架内补 **对话点**（每条只补一句，避免资产膨胀）：

| 缺口类型 | 建议挂接 | 用途 |
|---|---|---|
| 最易被误归的同名带 | 2504.13816 | 在区隔段显式点名，说明本纲领不处理"知识边界识别" |
| 强经验旁证（能力≠应用） | 2610.31060、2610.28539 | 支撑"边界不因规模消失" |
| 盟友（反单一指标） | 2609.39717 | 支撑"边界不可化约为评分" |
| 对话点（边界双向失效） | 2610.08662（过度防御） | 支撑"边界既可能过宽也可能过窄" |
| 形式化支点 | 2609.09306 | 支撑"结构 → 可及范围"的推导路径 |
| 工程原型（不变量内核） | 2610.30557 | 支撑"边界作为不可变约束"的可行实现 |

**处置原则：** 以上六项为**对话点/旁证**，不进入 PRIOR_ART 的 14 条主坐标；若后续需扩充主坐标，优先考虑 2609.09306（形式化）与 2610.31060（经验）。

---

# 7. 术语空位的证据强度

| 判据 | 结果 | 强度 |
|---|---|---|
| 精确短语 "boundary cognition" 窗口内新发 | 0 | 强 |
| "cognitive boundary" + hypothesis | 0 | 强 |
| "mind has a boundary" | 0 | 强 |
| "assembled intelligence" | 0 | 强 |
| 邻近带"boundary"占用 | 65/674 | 说明词面拥挤、命题空缺 |
| 全时段唯一近似 | 1 条（2025-04，语义不同） | 中等（需持续监控，可能被后续工作命名占用） |

**结论：术语空位可写入本纲领的贡献声明，但表述应限定为"截至 2026-10-26 的 arXiv 检索未见同名纲领"，不得表述为"无人研究边界"。** 后者与事实不符——邻近带 65 篇正在研究各种边界。

---

**说明**：本核查为采样性质，x2/x3/x5 三组查询触达检索接口单次返回上限，故题录计数不可作穷尽性统计。采集脚本与题录原始数据不在本仓库内。
