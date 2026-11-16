# EFG finite computation — ordered implementation prompts

这些提示词承接已完成的 [A–F 迁移](efg-computability-migration.md)，按
**G → H → I → J → K → L → M → N → O → P → Q → R** 执行。每次复制“共同约束”和一个
提示词，或让执行者阅读本文件后只执行指定任务。生成本文件不等于已经执行这些任务，
也不代表重新开放 Canonical/Frontend API 增长。

G 已于 2026-09-03 正式完成：同一 219 模块完整环境扫描确认不可计算身份
140 → 138，恰好移除两个目标且无新增；详见
[G 交付记录](efg-computability-migration.md#g-checkpoint--2026-09-03)。
H 已于 2026-09-03 在现有 opt-in 示例中实现并证明：可计算的充分 fuel、结构递归
总求值器，以及任意充分 fuel 下与原有求值器的等价定理，均见
[H 交付记录](efg-computability-migration.md#h-checkpoint--2026-09-03)。
I 已于 2026-09-03 在 opt-in 示例中证明有理有限期望与实际有限加权 Dirac 测度的
积分相等，并验证可积性、归一性、事件概率及语义等价不变性；见
[I 交付记录](efg-computability-migration.md#i-checkpoint--2026-09-03)。
J 已于 2026-09-03 在 opt-in 示例中把完整历史的有限执行分布接到实际解析路径律，
并证明有理停止收益等于现有 `stoppedUtility` 的积分；见
[J 交付记录](efg-computability-migration.md#j-checkpoint--2026-09-03)。
K 已于 2026-09-03 在 opt-in 示例中实现有限观察后验、完整历史上的继续执行和有理条件收益，
证明 Bayes 公式、联合执行条件化等价及实际解析有限窗口积分对应；见
[K 交付记录](efg-computability-migration.md#k-checkpoint--2026-09-03)。
L 已于 2026-09-03 在 opt-in 示例中从有界终止的有限历史分布实际构造吸收路径分布，
证明全部自然数时刻的边缘对应，并构造既有 supplied-law 接口的测度与合法性证书；见
[L 交付记录](efg-computability-migration.md#l-checkpoint--2026-09-03)。
M 已于 2026-09-03 在 opt-in 示例中实现有理停止期望、`M*q_H` 误差证书和有预算搜索，
证明与实际路径律上既有 eventual utility 的积分对应，并复用几何终止例子验证；见
[M 交付记录](efg-computability-migration.md#m-checkpoint--2026-09-03)。
N 已于 2026-09-03 在 opt-in 示例中把显式有限的根绑定策略表接到现有纯 Nash
检查器，证明完整纯偏离空间的正确性，并连接 occurrence 收益和既有逆向归纳；见
[N 交付记录](efg-computability-migration.md#n-checkpoint--2026-09-03)。
O 已于 2026-09-03 在 opt-in 示例中实现固定有限有理 Markov 链的多步吸收检查、
Cramer 求解、首次终止分布，以及唯一性、可积性和收益/时间期望对应证明；见
[O 交付记录](efg-computability-migration.md#o-checkpoint--2026-09-03)。
P 已于 2026-09-03 完成 G–O 的算法/前提/消费者审查和全量复验；227 个模块保留
相同的 138 个不可计算身份，11,366 个声明无禁用公理依赖，两份基线未改；见
[P 最终审计](efg-computability-migration.md#p-final-semantic-and-computability-audit--2026-09-03)。
A–P 共 16 步，现已在各提示词明确的范围内全部完成。具体分析边界、外部数据接口和
剩余范围限制见最终审计，不以不可计算数量变化替代算法和数学语义证明。

Q、R 是 2026-09-03 严格复审后新增的两个任务。Q 已在现有 opt-in 示例中完成：
从几乎必然终止证明误差收敛，执行无需预算的最小 horizon 搜索，并证明原 eventual
utility 的积分误差；见 [Q 交付记录](efg-computability-migration.md#q-checkpoint--2026-09-03)。
R 已在现有两个有限 Markov opt-in 示例中完成：自动计算 `k=n+1` 与精确有理
生存界，证明全域吸收判定的充要条件，并复用实际首次终止收益/时间语义。
见 [R 交付记录](efg-computability-migration.md#r-checkpoint--2026-09-03)。
临时探针不计入交付。复审范围、证据和两项任务必须保留的数学条件见
[Q/R 前语义审查](efg-proof-audit.md#pre-qr-semantic-review--2026-09-03)。

| 提示词 | 目标 | 主要产出 |
|---|---|---|
| G | 落实两个可消除身份 | 显式 Countable 证明、有理数中点、更新审计证据 |
| H | 完整有限随机树求值 | 足够 fuel、总求值器、与有界求值器等价 |
| I | 有限期望与积分连接 | 有理有限求和与有限原子测度积分相等 |
| J | 有限执行与有界解析收益连接 | 实际边缘分布对应、停止收益对应 |
| K | 有限条件继续收益 | 后验、继续执行、期望及正概率对应证明 |
| L | 有界终止的完整路径分布 | 从有限历史构造合法吸收路径律 |
| M | 截断期望误差证书 | 可计算未终止质量、误差界和有预算搜索 |
| N | 根绑定有限策略均衡检查 | 有限策略表、纯 Nash 检查和正确性 |
| O | 有限有理 Markov 链特化 | 固定策略的最终收益和期望终止时间 |
| P | 全部结果的语义与证明审计 | 实现/假设/证明/缺口清单及复验 |
| Q | 正误差下保证终止的最终收益近似 | 从几乎必然终止推出误差收敛，实际搜索并证明积分误差 |
| R（已完成） | 自动有限 Markov 求解 | 计算吸收证书、证明判定完备性、复用实际收益/时间语义 |

## 共同约束

```text
在 EconCSLib 仓库根目录工作，只执行指定的一个任务。先阅读 AGENTS.md、README.md、
docs/design.md、docs/design/efg-document-authority.md、efg-minimal-core-freeze.md、
efg-governance.md、efg-semantic-universes.md、efg-proof-audit.md；后五个文件均位于
docs/design/。再读目标模块、导入、已有消费者和前序任务的交付记录。

先运行 git status --short --branch，保留全部已有工作区修改，不提交、不重置基线。
重新检查目标是否已经完成；若已完成，核实证据并报告，不重复增加接口。
通过 scripts/check_efg_computability.py 的完整环境扫描记录起始身份集。
--skip-build 只在 Lake 校验现有产物新鲜度后使用；失效时正常重建。

范围和架构：
1. 先复用 FiniteLaw 的 map、bind、expectRat、condition?、conditionOnFiber、
   expectRat_bind，以及现有执行、继续、耦合和策略对应定理。
2. Canonical/Frontend API 增长冻结仍有效。现有定义可以在保持接口或同步迁移消费者
   的条件下修正实现。新增能力先放入合适的 opt-in 示例或允许的 Experimental 模块，
   遵守模块登记和导入规则，不加入 EconCSLib.lean，不在 Examples 中伪装新增规范 API。
   若确实需要公开 API 增长，先完成可审查的实验结果，报告所需最小变化，不修改冻结
   政策、增长基线或审计范围来规避检查。记录原型与正式 API 的区别。
3. namespace 按数学对象归属组织，参考已记录的 Formech 风格；局部变量、实例、记号
   放在实际使用的 section 中。沿用已有命名，不增加无意义别名或全局实例。
4. Math/ 不依赖 EFG。FiniteLaw 核心保持可执行且不引入解析栈；测度解释和对应证明
   放在下游。尽量在定理表达式中复用已有测度构造，不新增分析包装身份来挤压基线。

数学和可计算性：
5. 有限时域、有限支持、有限状态、有限信息集分别说明。前向有限支持执行通常不需要
   全局 Fintype State。计算所用枚举、Decidable、策略和收益必须实际可执行；仅有
   Finite/Countable 或存在性证明不算算法输入实现。显式可枚举空间上的可判定搜索
   可以用 Prop 中的存在性证明保证终止，例如 Nat.find；必须真正执行搜索，且证明
   存在性来自本任务允许的前提，不能用 Classical.choose 直接提取答案冒充搜索。
6. 概率使用精确 ℚ≥0，数值期望优先使用 ℚ。一般 ℝ 参数只表示给定数学输入；不得
   因有限个实数运算就宣称能够输出任意实数的有效数值近似或执行实数比较。
7. 保留完整历史、动作 occurrence、信息一致性和绝对时间。没有充分性/Markov 证明，
   不合并端点相同的历史，不把继续执行改成从时间零重启。
8. 零概率条件返回 none/明确的部分结果；预算耗尽不等于永不终止。Option 中的 none
   与真实收益零保持区分；将未终止收益约定为零时，明确这是停止收益的定义。
9. 不把原来证明的合法性、归一性、边缘一致性或存在性改成调用方新增假设。有限特化
   可以有明确的新适用条件，但一般接口和原前提下的既有结论必须保留。每个新证书
   都要说明其来源，不能把目标等式作为输入后称为算法正确性证明。
10. 不使用 sorry、admit、新公理或其他跳过检查的手段。公开数学证明不用 native_decide；
    可用它做匿名运行回归。经典推理可用于证明，不能替代运行时选择。禁止新增不可计算
    身份、扩大基线或通过移动/改名/改扫描范围隐藏身份。若遇到此冲突，保留分析定义，
    把有限算法和证明放到允许的范围内，并报告真实限制。

验收：
11. 真正实现算法，证明目标数学性质，再做能区分正确/错误语义的少量回归；不要只测
    实现的同义改写。优先覆盖零概率、终止边界、同端点不同历史、时间偏移和非平凡数值。
12. Lean 修改运行 lake build、lake build EconCSLib.Examples、
    lake env lean tests/FiniteLawSmoke.lean，以及 scripts/ 下的
    check_lean_placeholders.py EconCSLib、check_efg_api_growth.py、
    check_efg_computability.py、check_efg_axioms.py、check_efg_governance.py
    （Python 脚本用 python3 执行）。对更改模块分小批运行 lake env leanchecker 模块名。
    检查器变更再运行对应单元/集成测试。只改文档则检查链接、声明和计数，不重复构建。
13. 如新增 opt-in 模块，确认完整构建、计算性扫描和公理扫描均覆盖它；不要缩小扫描。
    检查新算法的 Lean.isNoncomputable 结果。只在重新审阅源码后更新分类中的范围/哈希
    和当前计数，保留旧迁移记录及两个既有 baseline 文件。
14. 所有修改运行 git diff --check；交接前再次检查 git status --short --branch。
    报告实际前后身份数、算法输入/输出、数学假设、证明、消费者迁移、检查结果和缺口。
    文档不得把临时原型或条件成立时的定理写成已具备的一般能力。
```

## 提示词 G — 落实两项明确清理

```text
遵守共同约束，只处理以下两个候选。

1. EconCSLib/Examples/ExtensiveGame/ObservedMeasurableKernelAlmostSureOutcomeBoundary.lean
   的两状态 Node：保留 DecidableEq，把 deriving Countable 改为 Prop 中显式的
   active ↦ 0、terminal ↦ 1 单射证明，消除自动派生的不可计算编码辅助函数。
   保持 Countable Node 的用途、实例可用性及原有历史可数性/可测性证明。
2. EconCSLib/Examples/ExtensiveGame/ObservedNonAtomicKernelBoundary.lean 的 halfAction：
   使用 ((1 / 2 : ℚ) : ℝ) 构造同一个区间中点，去掉该定义的 noncomputable。
   证明它仍等于实数 1/2；迁移依赖实数除法定义相等的消费者，不改变事件或概率。

临时副本已分别显示局部身份数 2→1、16→15；以当前完整环境为准，不硬编码数量。
核对两个目标身份消失、没有新身份。检查标准公理依赖，保留所有下游结论。
更新分类的移除身份、保护清单、当前快照和受影响证据；保留 A–F 的历史记录。
若起点仍是 140，预期结果为 138。这不代表给执行器增加了 Countable 编码需求。
```

## 提示词 H — 完整有限随机树求值

```text
遵守共同约束，处理 StochasticGameTree 的有限树求值。读取
EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean 及其编译器和消费者。

1. 利用 child : Fin (arity + 1) → StochasticGameTree N 的可枚举定义域，结构递归
   计算足够 fuel：Leaf 为 1，Player/Chance 为 1 加所有孩子所需 fuel 的最大值。
   当前求值器 fuel=0 连叶子也返回零，因此不要把叶子的足够 fuel 设为零。
2. 在允许的原型范围内给出不需要外部 fuel 的结构递归求值器，保留 path 参数及
   chance 节点的精确权重。不得通过 Classical.choose 提取深度或选择孩子。
3. 证明每个孩子的 fuel 严格更小，并证明对任意 policy/path/player，若
   requiredFuel tree ≤ fuel，则总求值器等于现有 expectedPayoffWithFuel。
4. 不改变原有不足 fuel 时的语义。修正“孩子函数不透明，因此无法计算最大深度”的
   过强注释；不要以此把已有有界接口或定理直接删除。

回归至少包含叶子、不同深度的分支、非退化 chance 权重，以及同子树不同 occurrence
的策略选择。验证新函数不是 noncomputable。临时原型的存在不能替代正式证明。
此任务增加完整有限树能力；原求值器已可执行，不预设不可计算总数下降。
```

## 提示词 I — 有理有限期望与解析积分相等

```text
遵守共同约束，复用 FiniteLaw/Core.lean 中的 FiniteLaw.expectRat，完成有限原子测度
的期望对应证明。

1. 搜索已有有限求和、Dirac 积分、测度加法和缩放定理。使用已有的有限加权 Dirac
   解释；若没有可复用名称，在允许的下游原型中表达，不在 FiniteLaw 核心引入 Measure。
2. 对 L : FiniteLaw α 和 u : α → ℚ，在离散可测空间或足够的可测性条件下证明：
   ∫ x, (u x : ℝ) ∂μ_L = (L.expectRat u : ℝ)。
   同时证明所需可积性、归一性和事件概率对应；μ_L 必须由 L 的原子实际定义。
3. 不要求整个 α 有限。正确处理重复原子和零权重；表示等式与 FiniteLaw.Equivalent
   分开，结果应对 Equivalent 不变。
4. 计算数据仍由 expectRat 产生；测度和积分只出现在下游语义及证明中。不要新增一个
   同义的不可计算期望定义，再宣称实现了计算。

回归使用含重复原子、零权重、负收益和非整数期望的有理实例。
证明通过内核检查，计算结果可实际运行；记录每个可测性条件为何需要。
```

## 提示词 J — 有限执行与有界解析收益相等

```text
遵守共同约束，基于 I，把有限执行结果接到实际解析模型，而非接到假设目标等式的包装。
读取 Execution/StochasticExecution、Simulation/Kernel/DiscreteBridge、Kernel/Arena、
Simulation/Equilibrium/Outcome，以及相关 chance/behavioral 编译和实现定理。

1. 在显式可执行策略、终止判定及有限有理转移的范围内，复用 finite executor 得到
   每个 horizon 的完整历史分布，复用 expectRat 计算有理停止收益。
2. 从具体模型的一步转移对应和初始条件出发，对 horizon 归纳证明有限历史分布的
   测度解释等于相应解析坐标分布。逐一处理终止吸收和实际动作历史。
3. 结合 I 证明有界停止收益计算等于现有 stopped utility 的解析期望。收益必须来自
   同一个终止收益函数；未终止取零仅用于这个明确声明的停止收益。
4. 如果当前桥接接口需要 supplied/path realization 证书，区分“利用已有证书的
   推论”与“本任务实际构造的证书”。不得将要证明的边缘等式再次作为新前提完成任务。
   一般解析模型需要的额外条件明确列出，不声称覆盖任意非原子核。

至少完成一个非退化随机实例，证明数值收益并跑出结果；检查 horizon=0、提前终止、
非终止收益非零但停止收益为零，以及相同端点但历史不同的收益。
```

## 提示词 K — 有限条件继续收益

```text
遵守共同约束，基于 I、J，实现有限窗口的条件继续计算及正确性。
先读 FiniteLaw/Conditioning、Observed/KuhnConditioning、Simulation/Continuation/
ObservedConditioning 和现有 ConditionalEvaluation，复用已有后验及执行拼接。

1. 对时间 t 的有限历史分布、可执行观察函数 observe 和可判等的观察值 y，使用
   conditionOnFiber 计算后验。随后在每个后验历史上继续同一策略 H 步，再计算收益。
2. 零概率观察返回 none。正概率时证明归一性、Bayes 公式，以及与“联合有限执行
   再按该观察条件化”得到的结果相等。
3. 继续策略接收实际完整历史与原始时间；不能只拿当前状态，不能默认为 fresh restart。
   若只观察信息集而非完整历史，应对所有一致历史按后验权重计算。
4. 用 J 的实际语义对应构造有限窗口的条件期望正确性证书。明确 evaluation 只依赖
   指定有限窗口，不将它推广到任意无限路径效用。不要仅提供证书参数的投影函数。

回归覆盖零/正概率观察、共享端点的两个历史、相同观察下不同后续收益，以及
时间偏移会改变策略选择的情况。保留已有离路径信念的独立语义。
```

## 提示词 L — 有界终止下构造完整路径分布

```text
遵守共同约束，在 Arena.StochasticHistoryPolicy 的有限支持执行范围内实现：
给定当前历史 current、统一界 H，以及 H 步分布中所有正权重历史均已终止的证明，
实际构造由有限多个合法吸收路径组成的分布。

1. 从执行得到的完整终止历史重建各时间坐标，并在终止后恒等延续。复用
   CompletePlayFromHistory.stutter、prependHistory 和已有历史前缀操作。
   明确坐标零是 current；历史的绝对长度偏移不能被忽略。
2. 先构造可执行有限路径数据/FiniteLaw，再在下游给出测度解释。路径坐标按需计算，
   不枚举无限数组，不要求无限路径的 DecidableEq。
3. 正确删除或处理零权重原子；不能从零权重的非终止历史伪造合法完整路径。
4. 证明归一性、初始坐标、每一步合法性、终止吸收，以及所有自然数时刻的边缘分布
   与原执行器对应；覆盖 n≤H 和 n>H。构造既有 supplied-law 接口所需的实际证书。

不能假设目标完整路径律或最终 realization 等式。统一终止界只适用于本特化，
不得施加到一般无限执行接口。用不同终止时间的分支和非空 current 做回归。
```

## 提示词 M — 截断期望的有效误差证书

```text
遵守共同约束，利用 I、J；L 只作为有界终止特例，不能把统一终止界当成本任务前提。

设终止收益绝对值至多可计算有理常数 M≥0，U_H 在 H 时刻未终止时取零，U∞ 为现有
eventual utility。对相应路径律明确提供/证明：几乎处处合法，任一终止历史一旦到达
就保持，及原接口所需的最终终止条件。用 J 连接有限未终止质量 q_H 与 Pr(T>H)。

1. 证明 |E[U∞] - E[U_H]| ≤ M * q_H。先证明路径上的差异只可能出现在 H 尚未终止
   的事件，再证明可积性及积分不等式。不要遗漏吸收条件，也不要对任意两种有界
   效用误用这个常数 M；一般差异可能需要 2M。
2. 用 noneMass 和 expectRat 返回有理中心值及误差上界，并给出其正确性证明。
3. 对 ε>0 和明确搜索预算，搜索满足 M*q_H≤ε 的 H，返回可验证结果或预算耗尽。
   失败不等于过程不终止；没有有效收敛依据时不承诺任意预算成功。
4. 复用 repeat-or-stop 的几何终止例子验证 q_H=2^(-H)，另测终止已发生和预算不足。

数值算法不调用一般积分来取得中心值；积分保留在语义证明中。
```

## 提示词 N — 根绑定有限策略的均衡检查

```text
遵守共同约束，复用 StrategicGame/Checker 的 isNashEq/isNashEq_iff、已有逆向归纳
和 occurrence 编译器，构造一个可执行的有限 EFG 纯 Nash 检查实例及其一般原型。

1. 显式枚举玩家、当前根相关的 represented information 和合法动作，形成有限纯
   策略表。保留一个信息集内的动作一致性与不同 occurrence 的语义。
   GameTree.PlayerStrategy 是全局函数空间，不能因为输入树有限就直接声称它有限。
2. 用有限执行与有理期望评估每个纯策略组合，接到现有 checker；证明检查结果当且
   仅当此有限策略空间内无人有盈利单边偏离，并明确与原 EFG 偏离空间的对应。
3. 不声称纯 Nash 一定存在。逆向归纳和 SPE 仅用于其适用的完全信息/合法子博弈
   条件；不将它推广到任意不完全信息游戏。
4. 本任务不求解一般混合均衡。若扩展为检查给定有理混合候选，应另证期望对混合
   纯策略偏离的线性性；行为策略转移只在已有 recall/realization 条件下使用。

回归至少覆盖一个有纯 Nash 的实例、一个无纯 Nash 的实例和信息一致性约束。
用 kernel-checked soundness/completeness 定理连接 Bool 结果，不能只报告枚举输出。
```

## 提示词 O — 固定有限有理 Markov 链的最终收益

```text
遵守共同约束，本任务只研究固定策略下的有限 Markov 链，不做 MDP 优化、一般随机
博弈均衡或任意历史依赖过程。先搜索 Mathlib 和仓库的有限矩阵/有理消元工具。

1. 使用显式有限状态编码和每行归一的有理转移，终止状态吸收，终止收益为状态函数。
   若来自 EFG，先证明策略平稳且所选状态包含所有影响转移/收益的记忆；不能按原始
   端点合并历史。限制到指定初始支持可达的状态时，也应证明该限制保持执行。
2. 明确有效吸收条件，例如已验证的步数 k 和 ε>0，使每个相关非终态在 k 步内
   终止的概率至少为 ε。该证据可以计算/证明，不能从“状态有限”推出。
3. 设非终态转移块为 Q、到终态的块为 R、终止收益向量为 g，构造并求解
   (I-Q)v=Rg 和 (I-Q)t=1；终态的 v=g、t=0。实现实际有理求解，不使用不可计算
   逆矩阵，不能只把候选解或逆矩阵作为调用方输入。
4. 证明吸收条件支持可逆性/解的唯一性，并证明 v、t 分别等于最终收益期望和
   终止时间期望。校验残差只是其中一环，不能代替概率语义和可积性证明。
5. 无法满足所声明适用条件时给出明确错误/限制；不在奇异情形静默返回零。

回归包括几何自环后终止、多个终止收益、立即终止，以及存在不可终止闭合类的拒绝
案例。求解器只做到本任务需要的范围，不顺带建立新的通用线性代数框架。
```

## 提示词 P — 最终数学语义与计算性审计

```text
遵守共同约束，审查 G–O 实际完成的结果，不把计划、临时文件或未闭合的证明算完成。

1. 为每项记录：实际算法输入/输出、可执行实例来源、数学前提、已证明的对应定理、
   真实消费者及运行回归。区分有限数据计算、分析解释、外部证书和未完成目标。
2. 特别检查：重复/零权重原子、Option 的 none、fuel 的叶子边界、正概率条件化、
   同端点不同历史、继续与重启的时间、无限路径的吸收、SPE 的适用域、Markov 充分性、
   矩阵求解的唯一性，以及 M*q_H 误差界的准确前提。
3. 全量运行构建、占位检查、API 增长、计算性、公理与治理检查；对改动模块分批
   leanchecker。查明所有非标准公理依赖，公开证明不得依赖 native_decide 生成公理。
4. 对照起始身份集，报告实际删除、保留、新出现的身份；任何新身份必须解决，不能
   扩大基线。核对增长基线和计算性基线保持不变，全部新增 opt-in 模块都进入扫描。
5. 更新真实的当前分类证据与迁移记录，保留 A–F、G 等阶段的历史数字。审查 namespace
   是否符合数学归属，是否有无意义别名、泄漏实例或隐藏在示例里的正式 API 增长。

最终报告给出已实现能力、证明范围、剩余分析定义及具体缺口。若某个目标没有实现，
如实标明；不能用外部提供目标等式的接口、通过编译或 noncomputable 数字下降来替代
数学正确性与任务完成证据。
```

## 提示词 Q — 正误差下保证终止的最终收益近似

```text
遵守共同约束，只执行 Q。先读 docs/design/efg-proof-audit.md 的 Q/R 前审查，以及
EconCSLib/Examples/ExtensiveGame/ 下的 FiniteLawIntegral.lean、
FiniteExecutionIntegral.lean、FiniteTruncation.lean；再读
EconCSLib/GameTheory/ExtensiveGame/Execution/InfiniteTrajectory.lean 和
Simulation/Equilibrium/Outcome.lean。完整保留 M 的有预算搜索及其失败语义。

目标：对现有完整历史执行器、同一个当前历史 current、可计算有理终止收益和正有理
误差 ε，实际返回 H、中心 a_H 和半径 r_H，使 r_H≤ε，并证明 a_H 逼近现有路径律下
原 eventualUtility 的积分。无需调用方提供 horizon、预算、收敛速度或有效模量。

适用条件与语义：
1. 复用有限有理 StochasticHistoryPolicy、实际 terminal Decidable、完整历史和原
   stochasticHistoryLawFrom。数值计算不要求整个状态或历史空间 Fintype。
2. 主正确性入口沿用 FiniteTruncation.estimate_correct 的原条件：离散、可数的完整
   历史；BoundedTerminalPayoffExtension；有理收益在终止历史上与原 payoff 相等；
   可计算 bound : ℚ≥0 支配 extension.bound；同一实际 history Kernel.traj 下的
   几乎必然终止 hreaches。Countable 和分析条件只用于证明，不抽取运行时编码。
3. ε>0 是保证终止的条件。不要声称任意过程都终止、ε=0 的搜索都成功、能返回精确
   实数期望，或几乎必然终止必然给出有限 E[T]。本任务不要求有限 E[T]。

必须完成的证明链：
4. 令 B_H={path | ∀ t≤H, path t 尚未终止}。证明它可测且随 H 递减，交集恰为永不
   到达终态的路径。利用实际路径律的归一性、hreaches 及测度从上连续性，证明
   μ(B_H)→0。复用 measure_no_hit 将它识别为 q_H=Arena.noneMass policy current H。
   注意“时刻 H 未终止”的集合对任意原始路径未必逐点递减；必须通过 B_H 和已经
   证明的几乎处处吸收连接，不能忽略这一步。
5. 显式处理 ENNReal、实数和有理数转换，证明 bound*q_H→0。因此每个 ε>0 都存在
   H 满足可判定的有理不等式 bound*q_H≤ε。不能把这个存在性、q_H→0、搜索成功、
   目标积分等式、合法性或边缘一致性重新要求为调用方新增前提。
6. 用 Nat.find 或已有可验证顺序搜索实际计算最小这样的 H。Prop 中的存在性只作
   终止证明；计算仍按 H=0,1,... 检查精确有理数。允许内部通用搜索辅助函数接受
   该证明，但最终对 EFG 的入口必须由第 4–5 步从原 hreaches 推出它。
7. 复用 estimate 得到中心和半径，再复用 estimate_correct 证明
   |∫ U∞ dμ - a_H| ≤ r_H ≤ ε。积分、μ、U∞ 均与 M 的原始语义相同，不能把目标
   期望改定义成算法结果。数值实现不调用积分、极限、Classical.choose 或实数比较。
8. 证明搜索的最小性，以及它与原 searchHorizon/search 的关系：budget>H 时旧接口
   返回同一个结果；budget≤H 时旧搜索返回 none。保留旧接口在 ε=0 时的原有行为。

验收回归：
9. 使用真实 repeat-or-stop 执行器的 q_H=2^(-H)，验证 ε=1/8、bound=1 时最小 H=3，
   budget=3 失败、budget=4 成功；消费新积分误差定理，不能只运行通用半径函数。
10. 覆盖已经终止的 current、bound=0、非空 incoming history/绝对时间和负终止收益。
    保留“每个有限 H 都有未终止质量”的例子，表明新算法不依赖统一有限终止界。
    这些场景应验证实际算法；公开数值等式通过内核检查。

实现放在现有 FiniteTruncation 示例或聚焦的 opt-in 示例扩展中，不加入冻结的
Canonical/Frontend API。保持 FiniteLaw 核心无解析依赖。读取并复用 Mathlib 的
tendsto_measure_iInter_atTop、ENNReal 连续转换和 Nat.find API，不另建一般搜索框架。

运行共同约束中的完整验证和改动模块内核重放。确认新数据函数可编译且未标记
noncomputable，两个 baseline 不变。新增模块必须进入全量扫描；只在源码复审后
更新必要的分类证据。报告实际函数、完整前提、存在性来源、终止与误差证明和运行
结果；无运行时间上界不妨碍终止性，但不能把它写成复杂度保证。完成 Q 后停止。
```

## 提示词 R — 自动构造吸收证书的有限 Markov 求解

```text
遵守共同约束，只执行 R。读取 docs/design/efg-proof-audit.md 的 Q/R 前审查，以及
EconCSLib/Examples/ExtensiveGame/FiniteMarkovChain.lean 和
EconCSLib/Examples/ExtensiveGame/FiniteMarkovChainSemantics.lean。
Q 与本任务的证明相互独立；若 Q 已完成，保留其改动，不重复实施 Q。

目标：给定现有 Chain n m 的精确有理 Q/R、归一性和终止收益，自动决定整个给定
非终态域是否几乎必然吸收；成功时自动调用原 solve，返回最终收益和终止时间期望。
调用方不再提供 k、c、吸收证明、可逆性、候选解或收敛率。

范围必须精确：
1. 沿用固定有限 Markov 模型及 Fin n / Fin m 编码，不把任意 EFG 按端点商化，不做
   MDP 优化、策略选择或隐式可达状态裁剪。判定针对全部 Fin n；某个不可达坏分量
   仍应导致全域判定失败。失败不表示每个起点都无法吸收。
2. s_H(i)=∑j (Q^H) i j 是原 run_survival 证明的有限执行未终止概率。用它定义并
   证明全域吸收性质：对每个 i，s_H(i)→0；与原 run_firstHit 对应的首次终止测度
   总质量为一建立联系。不能把 AbsorbsAll 定义成“自动检查返回 true”来冒充完备性。

推荐具体实现（若改变路线，给出同等完整的证明和明确理由）：
3. 计算 k=n+1，c=max({0} ∪ {s_k(i) | i:Fin n})。使用显式有限枚举和精确有理运算；
   空非终态域取 c=0。复用 admissible k c，成功后调用原 solve k c。
   不增加无限 horizon 搜索，不使用谱半径/实数比较或不可计算矩阵逆来运行算法。
4. 证明自动计算的 c≥0 且 c≤1，并证明自动检查成功当且仅当全域吸收。关键的有限
   维论证不能遗漏：所有状态都有正概率路径到终态时，可以删除重复的非终态，得到
   长度至多 n 的正概率终止路径；因此在共同 k=n+1 下每行生存质量严格小于一。
   可用正权有向路径/有限可达集合证明，不必创建新的通用图论框架。
5. 证明反向及失败含义：若有状态不能沿正权路径到达终态，其可达非终态区域保持
   全部概率质量，所以不满足全域吸收。至少给出失败蕴含存在一个不吸收状态的正式
   定理；不能把原 admissible 对某个人工 k、c 的失败直接当成永不吸收的证据。
   新算法的完备性必须适用于全部归一化非负有理 Chain，不只回归矩阵。

求解及概率语义：
6. 自动证书通过后，用 det_ne_zero 和 solve_correct 证明实际返回成功；singular
   分支在此不可达。保留原 solve/solveLinear 的明确错误语义和所有已有消费者。
7. 新成功定理必须说明实际返回值满足两个 Bellman 方程且唯一，并等于已有首次
   终止测度下原 reward 和实际时间 r+1 的积分；归一性、收益可积性、时间可积性
   都从计算出的证书推出。不能只验残差，也不能只重述“若原 solve 成功则正确”。
8. 时间索引沿用 run：inr (r,a) 表示在 r+1 步首次到达 a。初始已经终止的状态的
   收益为 reward a、时间为 0。此任务构造/使用首次终止律，不声称构造任意 EFG
   完整路径律。有限全域吸收带来的有限期望时间不能推广到一般无限历史过程。

验收回归：
9. 无外部 k、c 地运行原 geometric、twoRewards、delayed：分别核实选定起点的
   (收益,时间) 为 (7,2)、(1,2)、(7,3)，并消费新的概率语义定理。
10. 覆盖原 closedClass：起点 0 可终止而另一分量闭合，整个输入仍应拒绝；证明或
    检验这个区别。再覆盖 n=0 的终态输出、n>0 且 m=0 的归一化闭链、确定性多步
    吸收和一个很小但正的有理吸收概率。不能通过浮点容差把正概率当成零。
    n=0,m=0 的空状态域也要明确处理，不能通过隐含 Nonempty 假设绕开。

实现放在现有两个 Markov 示例或聚焦的 opt-in 扩展中，不升级为冻结的正式 API。
先完成精确算法与全域判定完备性，再连接 solve_correct；不把未证明的吸收判定
包装成可调用接口交付。运行共同约束中的完整验证与内核重放，检查新数据函数的
Lean.isNoncomputable；保留两个 baseline，更新经过源码复审的必要分类证据。
报告自动证书、判定的充要条件、失败见证范围、实际求解/积分定理及数值运行结果。
完成 R 后停止，不顺带实施起点可达裁剪或 EFG-to-Markov 编译器。
```
