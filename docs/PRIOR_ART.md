# 引用清单（PRIOR ART）

> 定位：不是学术礼节，是**资产负债表上的一次入账**。
> 目标：让清单提高净资产，而不是增加负债。

本文件所有坐标已于 2026-10-25 经 Crossref 逐条核验。front-matter 为机器可读版本，正文为人类可读版本；两者冲突时以 front-matter 为准，并立即修正正文。

## 一、估值框架：为什么引用是资产

净资产 ≈ **可核事实 / 主张范围**（分子越大越好，分母越小越好）

- 分子（可核事实）：56 文件 / 467 定理 / 0 sorry / 14-14 gate / 双锚 / 可复现。
- 分母（主张范围）：未划界时读者默认你主张了全部——包括闭包算子的数学、包括"心智就是这样"。
- 引用清单的唯一作用：**缩小分母**。分子一分不减，估值因此上升。

| 规则 | 含义 |
|---|---|
| 只有 credit 没有 delta 的引用 = 负债 | 只承认"这是别人的"，读者只会问"那你做了什么" |
| 有 delta 的引用 = 资产 | 承认来源 + 精确划出自己的窄区，claim 密度上升 |
| 未声明的标准对象 = 表外资产 | 已用它支付了 467 定理的成本，却没入账，估值被系统性低估 |

结论：**引用不是还债，是审计。**

## 二、L0 工具层（可复算的前提）

| # | 坐标（已核） | credit | delta | 落点 |
|---|---|---|---|---|
| P01 | de Moura & Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE-28, LNCS 12699, Springer, 2021, pp. 625–635. DOI 10.1007/978-3-030-79876-5_37 | 证明检查器与语言 | 无（工具，不主张） | README / VERIFICATION |
| P02 | The Mathlib Community, *The Lean Mathematical Library*, CPP 2020, ACM, pp. 367–381. DOI 10.1145/3372885.3373824 | 代数与序结构库，本工作依赖其接口 | 无（工具） | README / lakefile |
| P03 | `vendor/CausModel`（第三方源码，非文献） | 范畴论依赖源码 | 无（注明来源与许可） | SCOPE / PROVENANCE |

## 三、L1 数学对象层（标准对象，不主张新颖）

| # | 坐标（已核） | credit | delta | 落点 |
|---|---|---|---|---|
| P04a | Moore, *Introduction to a Form of General Analysis*, AMS Colloquium Publications 2, 1910, pp. 1–150. DOI 10.1090/coll/002/01 | "边界 = 闭包不动点集"这一形式本身 | 不主张该数学。主张限于：把 `Fix(c)` **当作边界的定义**，并要求判据与它同一 | technical §Prior art |
| P04b | Birkhoff, *Lattice Theory*, AMS Colloquium Publications 25, 1940. DOI 10.1090/coll/025 | 同上（格论体系化表述） | 同上 | 同上 |
| P05 | Tarski, *A lattice-theoretical fixpoint theorem and its applications*, Pacific J. Math. 5(2), 1955, pp. 285–309. DOI 10.2140/pjm.1955.5.285 | 完备格上单调映射的不动点存在与最小不动点 | 用其存在性，不做新的格论；新在把不动点集读作**边界**并加判据 | 同上 |
| P06 | Cousot & Cousot, *Abstract interpretation…*, POPL '77, ACM, pp. 238–252. DOI 10.1145/512950.512973 | 阈值判据 `{b ≤ θ}` 与抽象域水平集同构；可靠的近似语义 | 抽象解释求**可靠近似**；我们求**同一性条件**：边界与报告何时不可分离，并给出其一般不成立的反例族 | 同上 |
| P07 | Davey & Priestley, *Introduction to Lattices and Order*, 2nd ed., Cambridge UP, 2002. DOI 10.1017/CBO9780511809088 | 术语标准化 | 无 | 脚注 |

## 四、L2 问题谱系层（谁已经在问"边界自守系统"）

| # | 坐标（已核） | credit | delta | 落点 |
|---|---|---|---|---|
| **P08** | Maturana & Varela, *Autopoiesis and Cognition: The Realization of the Living*, Boston Studies in the Philosophy of Science 42, D. Reidel, 1980. DOI 10.1007/978-94-009-8947-4 | "自守系统"与"边界由系统自身维持"；问题式与它同源 | 该理论是**定性的组织闭合**：无判据、无反例、不可机检、不区分"边界"与"对边界的报告"。我们给出可判定的 gate、显式 scope、14/14 可复算的拒绝规则 | technical §Prior art（**必列**） |
| **P09** | Friston, *Life as we know it*, J. R. Soc. Interface 10(86), 2013, 20130475. DOI 10.1098/rsif.2013.0475 | 边界的概率化形式：条件独立分区 | blanket 是**统计分区**，不含"报告"。我们加的是报告—边界同一性，以及拒绝版本拼接的 R3/R4 | 同上（**必列**） |
| P10 | Rosen, *Life Itself*, Columbia University Press, 1991. ISBN 978-0-231-07564-0（无 DOI） | 自指闭合与代谢—修复闭环 | 定性；只保留"闭合"的可判定部分 | 同上 |
| P11 | von Foerster, *Observing Systems*, Intersystems, 1981（无 DOI）；可核坐标用 *Understanding Understanding*, Springer, 2003, DOI 10.1007/b97451 | 观察者进入系统内部；自指的认识论地位 | 认识论命题；我们把它降为形式条件（报告是边界的函数） | 同上 |
| P12 | Powers, *Behavior: The Control of Perception*, Aldine, 1973. ISBN 978-0-202-25113-4（无 DOI） | 系统维护的是**被感知量**而非世界状态 | 控制论模型；我们关心该维护何时**失效可判** | 脚注 |
| P13 | Ashby, *Design for a Brain*, Chapman & Hall, 1952；2nd rev. ed. 1960（DOI 指后者 10.1037/11592-000） | 适应作为参数空间搜索；"维持"的动力学基础 | 连续动力学；我们给离散闭包族下的判定 | 脚注 |
| **P14** | Metzinger, *Being No One: The Self-Model Theory of Subjectivity*, MIT Press, 2003. DOI 10.7551/mitpress/1551.001.0001 | 系统内部的自我表征；"报告"作为被建模对象的地位 | 解释框架，无形式判据，不承诺任何现象属性。只给"报告与边界何时同一"的形式条件，**不声称证明了人的心智是此类系统** | technical §Scope（**必列**） |

## 五、L3 限制层（主动设限，最建立可信度）

| # | 坐标（已核） | credit | delta | 落点 |
|---|---|---|---|---|
| **P15** | Rice, *Classes of recursively enumerable sets and their decision problems*, Trans. Amer. Math. Soc. 74(2), 1953, pp. 358–366. DOI 10.1090/S0002-9947-1953-0053041-6 | 通用判定程序不可能 | **不做**通用判定器；只做"给定闭包族 + 给定 gate"的判定，scope 写成显式前提 | technical §What is not proved（**必列**） |

> P15 是这份清单里最贵的一条资产：主动声明"我不能做什么"，等于给所有 claim 买了保险。

## 六、五条必列项的 delta 写法（可直接入页）

1. **P04** — *We do not claim the closure operator, the fixed-point characterisation, or the threshold criterion as new mathematics. Our claim is narrower: that a boundary so defined is machine-checkably identical to the report it licenses, under stated scope conditions — and that this identity is where the usual argument fails.*
2. **P06** — *Abstract interpretation asks for a sound approximation. We ask for an identity condition: when the boundary and the report of it cannot be separated — and we ship a counterexample family showing that, in general, they can.*
3. **P08** — *Autopoiesis states that a system maintains its own boundary. It does not state when that maintenance can be decided, nor what happens when the report of the boundary drifts from the boundary. We give the decidable version, with an explicit gate and a reproducible pass count.*
4. **P09** — *A Markov blanket partitions a system statistically. It contains no notion of a report. Our addition is the identity between boundary and report, expressed as a rejection rule for stitched version/parent/evidence bundles.*
5. **P14** — *Self-model theory describes a system that represents itself. It is an explanatory framework, not a decision procedure, and we do not claim it. We claim only the formal condition under which a report and a boundary coincide, and we make no claim about human minds.*
6. **P15** — *By Rice's theorem no general decision procedure exists. We therefore do not offer one: every claim in this document is relative to a given closure family and a given gate, both of which are executable here.*

## 七、负面清单（不引，且说明为什么不引）

| 不进入的谱系 | 理由（对外表述） |
|---|---|
| IIT / GWT 等实证争论 | 本纲领不提供实证预测，不参与该类判定 |
| 任何"通用智能判定"路线 | 与 P15 冲突，见 §What is not proved |
| 人格 / 心理测量框架 | 不属于本纲领的对象域 |

## 八、附录：可选坐标（脚注层，已核）

| # | 坐标 | 用途 |
|---|---|---|
| A01 | Ward, *The Closure Operators of a Lattice*, Ann. of Math. 43(2), 1942, p. 191 起. DOI 10.2307/1968865 | 闭包算子谱系沿革（Crossref 仅收录起始页） |
| A02 | Turing, *On Computable Numbers…*, Proc. London Math. Soc. s2-42(1), 1937, pp. 230–265. DOI 10.1112/plms/s2-42.1.230 | 可计算性前提（1936 宣读 / 1937 出版） |
| A03 | Kirchhoff, Parr, Palacios, Friston, Kiverstein, *The Markov blankets of life*, J. R. Soc. Interface 15(138), 2018, 20170792. DOI 10.1098/rsif.2017.0792 | P09 的当代展开，优于预印本 |
| A04 | Clark, *Surfing Uncertainty*, Oxford UP, 2016. DOI 10.1093/acprof:oso/9780190217013.001.0001 | 预测加工综述 |
| A05 | Levin, *Technological Approach to Mind Everywhere*, Front. Syst. Neurosci. 16, 2022, 文章号 768201. DOI 10.3389/fnsys.2022.768201 | "心智无处不在"边界讨论 |
| A06 | Varela, *Principles of Biological Autonomy*, North-Holland, 1979. ISBN 978-0-444-00321-8（无 DOI） | 自治概念的生物学展开 |
| A07 | Hales et al., *A Formal Proof of the Kepler Conjecture*, Forum of Mathematics, Pi 5, 2017. DOI 10.1017/fmp.2017.1 | 大规模形式化先例 |
| A09 | Smith, Katz, Niemeyer, *Software citation principles*, PeerJ Comput. Sci. 2, 2016, e86. DOI 10.7717/peerj-cs.86 | 软件引用规范 |
| A10 | Wilkinson et al., *The FAIR Guiding Principles…*, Scientific Data 3, 2016, 文章号 160018. DOI 10.1038/sdata.2016.18 | 数据可复现规范 |

**A08（Gonthier 2008）暂不收录**：Crossref 命中的 10.1007/978-3-540-87827-8_28 是 AISC 2008 单页摘要（pp. 333–333），不足以作正式坐标。如需引用四色定理形式化，应改引 Notices of the AMS 55(11)（无 DOI），否则删除本条——不得用摘要页冒充论文页。

## 九、核验说明（本版新增）

1. 全部 DOI 由 Crossref REST API 返回，逐条比对题名、年份、卷期、页码，与本文件一致后方写入 front-matter。
2. 三条无 DOI 专著（P10 Rosen、P12 Powers、A06 Varela）改用 ISBN，并经图书馆书目/书商记录双源核对，ISBN-10 校验位全部通过，同时给出对应 ISBN-13。
3. P11 von Foerster 原版 1981 无可核坐标，改用 2003 Springer 文集 DOI，并在 `substitution_note` 中写明不得混为一书。
4. P13 Ashby 的 DOI 指向 1960 年第 2 修订版，非 1952 初版，版次必须一并标注。
5. 凡 Crossref 元数据缺项（如 A01 仅起始页、A05/A10 无页码），正文不得补写未经核实的数字。

## 十、一句话结论

引用清单不是向他人低头，是**给"门被推开"这句话标价**：越精确地说明哪一部分不是你的，剩下那一部分就越值钱。
*（内容由AI生成，仅供参考）*
