# EFG 算法实现台账

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

日期：2026-09-04。范围：EFG 主库；不含 `Examples/`。

本台账把
[算法机会审计](efg-algorithm-opportunity-audit.md)转成可执行工作项。它记录算法输入、
输出、数学方法、代码 owner、correctness 目标和实现状态。Lean 源码与通过的检查器决定
实际完成状态；本文件不把计划中的接口写成已有能力。

## 1. 状态与验收规则

| 状态 | 含义 |
|---|---|
| `已有` | 主库已有可执行定义，并有本台账所述范围的 correctness 证据 |
| `实现中` | 已分配具体 owner 和验收目标；尚未通过全部集成检查 |
| `待实现` | 数学算法明确，但主库 owner、bridge 或消费者尚未闭合 |
| `研究接口` | 算法需要先选择有效表示、事件语言或数值误差契约 |
| `分析保留` | 原 `Measure`、`Kernel`、积分或全域路径声明继续承担一般数学语义 |

每个算法项必须满足：

1. 运行定义只依赖明确的有效输入；证明可以使用经典逻辑，但不能用选择替代算法。
2. 精确算法返回 `FiniteLaw`、`ℚ`、`Bool`、`Option` 或其他明确可执行结构。
3. 无限对象使用统一有限查询、惰性采样或认证近似表示，不假装枚举无限数据。
4. bridge 必须是精确等式、误差界或注明定义域的几乎处处定理。
5. 原分析声明不因有效子域已有算法而改称 legacy，也不自动删除 `noncomputable`。
6. 每步通过目标模块构建、placeholder、computability、governance 和差异检查后才能改为
   `已有`。

## 2. 算法工作项

| 编号 | 关联声明 | 问题与有效输入 | 方法与输出 | 建议 owner | 状态 |
|---|---|---|---|---|---|
| A03 | S102、S104--S120、S123 | 有限动作／转移律、终点判定、完整前缀 | `map`/`bind` 一步执行并递归到任意给定 horizon；动作事件始终保留 occurrence | `Execution/Discrete/HistoryKernel.lean`、`FiniteObservation.lean` | `已有` |
| A04 | S088 | 有限有理先验、可判定 observation、正质量事件 | Bayes filter 后归一化；零质量返回 `none`；正质量 posterior 用绝对时钟续局 | `Execution/Discrete/ConditionalContinuation.lean` | `已有` |
| A05 | S089、S095--S097、S135--S138 | 可执行 event policy、指定前缀和 horizon | 绝对时钟 prefix、tail reindex、fresh restart、splice；每个查询精确终止 | `FiniteObservation.lean`、`Simulation/Restart/FiniteExecution.lean` | `已有` |
| A06 | S121--S122 | 有限 abstract law、依赖完整 event prefix 的有限 realization、终点判定 | `abstractLaw.bind realizationLaw` 后记录实际 action；以 dependent action fiber 保证合法性 | `Execution/Discrete/RealizedInformation.lean` | `已有` |
| A07 | S124--S126 | `MeasurablePresentation` 已证明的 player/chance `FiniteLaw` 局部等式与终点判定 | 直接读取原有限动作律并记录 action；analytic realization 只用于 correctness | `Execution/Discrete/ObservedChance.lean` | `已有` |
| A08 | S095--S097、S106、S110、S118、S125--S126、S131--S134、S137 | 对所有 horizon 统一可计算的有限前缀律 | `prefixLaw : horizon → FiniteLaw Prefix` 加截断一致性、柱事件质量和分析边缘等式 | `Execution/Discrete/EffectivePathLaw.lean` | `已有` |
| A09 | S106、S110、S118、S125--S126、S131--S133、S137 | 正权重支持在统一界内终止的 `KernelArena` event execution | 执行至界后把每个终止 event prefix 重放为吸收路径；返回有限支持的完整 event/state 函数律 | `Execution/Discrete/FiniteCompleteEventPath.lean` | `已有` |
| A10 | S090--S091、S098、S100 | 有理停止收益、可判定终点、可算未完成质量、收益界 | 精确中心与 `B·q_H` 半径；有预算首个时界搜索，或由存在性证明计算全局最小时界 | `Execution/Truncation.lean`、`Execution/Discrete/ContinuationTruncation.lean` | `已有` |
| A11 | S100 | 有限有理 Markov dynamics，可含非终止闭类 | 有限 reachability 剪枝；终点边界 `g`、不可达类边界 `0`，解有理线性方程 | `Math/Probability/FiniteMarkovChain/Reachability.lean` | `已有` |
| A12 | S100 | 与 A11 相同，给定起点 | 返回 `FiniteLaw (Option Terminal)`；`none` 质量为不终止概率；逐时首达用 `(Q^rR)_{ia}` 查询 | 同 A11 | `已有` |
| A13 | S100 | A11 的最终命中概率向量 `p` 与收益界 `B` | `lateHitMass H=(Q^H p)_i`，误差 `≤B·lateHitMass H`；允许正不终止概率 | 同 A11 的 semantics 叶 | `已有` |
| A14 | S090、S098、S101 | 因子化于有限 prefix 的有理 utility | 对 coherent prefix law 使用 `expectRat`，并证明 cylinder utility 的 horizon-invariance | `Execution/Discrete/EffectivePathUtility.lean` | `已有` |
| A15 | S090、S098、S101 | 有效柱函数／简单函数逼近及可算非负误差半径；原分析目标另给 exact finite marginals 与 uniform certificate | 搜索满足预算的首个前缀，以 `expectRat` 求精确中心；语义叶证明 prefix integral 等于 center，并从逐路径界推出 interval 与真实 tolerance | `Execution/Discrete/CertifiedPathApproximation.lean`；`Simulation/Kernel/CertifiedPathApproximation.lean` | `已有` |
| A16 | S090、S098、S101 | 有界逐期收益、有效有理 `0 ≤ γ < 1` | 一般 effective path 精确算时刻 `0..H-1` 并用 `B·γ^H/(1-γ)` 搜索；任意有限有理 Markov 链另精确解 `(I-γQ)v=r`，允许非终止闭类 | `Execution/Discrete/DiscountedPathUtility.lean`；`Math/Probability/FiniteMarkovChain/Discounted.lean` | `已有` |
| A17 | 不直接属于 58 项 | 有限策略域、有限 horizon、有理收益、可判定比较；`find` 另需显式 `FinEnum PureProfile` | `all` 用无重复 `Finset`；`find` 用有序 list 搜索；证明 membership／返回值的 soundness 与 completeness | `Observed/FinitePureNash.lean` | `已有` |
| A18 | 不直接属于 58 项 | 有限有理 Markov chain 与有限自动机／min-parity 目标 | 终止时 DFA 用 chain product 与 reachability；无限 min-parity 用正概率图、自动 SCC/bottom 分类并归约为两终点有理 Bellman 求解 | `Math/Probability/FiniteMarkovChain/Automaton.lean`、`Parity.lean` | `已有` |
| A19 | S082、S085、S086、S101；为其他核声明提供组合基础 | 模型选择 `EventCode`，提供 `EffectiveLaw`／逆像 `EffectiveMap`／expectation-transformer `EffectiveKernel`；观测量是有限有理 `SimpleObservable`，语义由 proof-only `Denotes`／`Represents` 证书给出 | `RatOracle` 返回任意正有理 tolerance 的有理 enclosure；结构递归计算 simple-observable 期望、pushforward、law bind 和 kernel composition；有理区间并给出精确非原子 uniform backend | `Math/Probability/Effective/{Enclosure,Core,Uniform}.lean`；独立 `Semantics` leaves；EFG `Simulation/Equilibrium/EffectivePathUtility.lean` | `已有` |
| A20 | S081、S092--S094、S130--S134 | 高层 `KernelBehavioralProfile` 的显式 effective 表示、arena 对应、机会律、终点判定和局部表示证书 | 装配 A06 的有限 realization policy，编译为 raw event policy，再复用 A05/A08；证明直连原 `compiledPolicy` 和路径边缘 | `Execution/Discrete/EffectiveKernelBehavioralProfile.lean` 与独立 semantics 叶 | `已有` |
| B01 | S099 原 raw-path 全域函数 | 任意无限路径 | `∃n∀m≥n` 为 `Σ⁰₂` 型且有限前缀不能决定；只保留分析定义 | 现有分析 owner | `分析保留` |

## 3. 分阶段实施

| 阶段 | 顺序 | 交付 | 当前状态 |
|---|---:|---|---|
| P1 | 1 | A01 finite profile law 与分析推前桥 | `已有` |
| P1 | 2 | A06 finite realization compiler 与局部 Measure bridge | `已有` |
| P1 | 3 | A07 chance presentation 直接离散 adapter | `已有` |
| P1 | 4 | 登记新模块、接入最窄内部聚合、运行完整 EFG gate | `已有` |
| P2 | 5 | A08 coherent effective path law | `已有` |
| P2 | 6 | A09 bounded complete event path | `已有` |
| P2 | 7 | A10 continuation truncation | `已有` |
| P2 | 8 | A11--A13 nonabsorbing finite Markov；EFG 编译后续接入 | `已有` |
| P2 | 9 | A20 high-level effective kernel-profile adapter | `已有` |
| P3 | 10 | A14--A16 effective path utility | `已有` |
| P3 | 11 | A17 finite Nash `find`/`all` | `已有` |
| P3 | 12 | A18 finite automaton objectives | `已有` |
| P4 | 13 | A19 有效事件／simple-observable 非原子概率接口及 EFG bridge | `已有` |

阶段顺序表示依赖和对外承诺，不要求内部开发机械串行。每一阶段完成后，在本表记录：
具体声明、有效输入、算法复杂度、桥接定理、消费者、验证命令及仍保留的分析边界。

## 4. P1 验收清单

- A01：不得把 `ProbabilityMeasure` 当作算法输出；finite marginal/outcome/path 必须能
  reduce，并分别证明与 S082/S085/S086 的分析结果相等。
- A06：terminal 必须可表达“无动作”；realization 可以随机且依赖完整 event prefix；
  编译后必须保留实际 action occurrence 和绝对时钟。
- A07：不得要求调用方提供已编译 kernel；直接动作律来自原 profile/chance law，现有
  `MeasurablePresentation` 的局部等式只用于证明与 S124 相等。
- 新运行定义不得新增 `noncomputable` 身份，不得反向导入积分或完整路径分析层。
- 每个新模块先单独通过 Lean，再运行 `lake build`、placeholder、EFG API growth、
  computability、axiom、governance 和 `git diff --check`。

## 5. 当前实现记录

本节记录已经落入主库源码并通过整库 gate 的工作；每项同时保留算法方法、correctness
证据、复杂度和没有被算法层替代的分析边界。

| 步骤 | 运行定义与方法 | correctness 证据 | 复杂度与仍保留的边界 |
|---|---|---|---|
| A01 | `FinitePureProfileLaw` 直接以 `FiniteLaw.map` 计算玩家 marginal、outcome 与完整 `CompletePlay` 原子 | `toMeasure_analyticMarginal`、`toMeasure_analyticOutcomeLaw`、`toMeasure_analyticPathLaw` 逐项证明 weighted-Dirac 推前等式 | 对原子表线性；一般非原子 profile measure 与任意路径事件仍在分析轨 |
| A02 | pure profile 用 `FiniteLaw.pure`，有限 mixed/player laws 用有序 dependent product 形成联合 profile law | pure、坐标 marginal 与 product 语义由 finite-law 定理及既有 mixed bridge 保持 | 联合支持最坏为各坐标支持大小乘积；没有把任意 measure 自动离散化 |
| A03 | `HistoryKernel` 用 terminal-aware `map`/`bind` 从完整 state/event prefix 递归到请求 horizon | 一步、任意 prefix、state/event coordinate 与分析 kernel executor 精确对应 | 时界固定时总会终止；完整历史与实际 action occurrence 一直保留，支持可指数增长 |
| A04 | 对有限正质量 Boolean observation 精确过滤、除以有理质量，再从后验 law 续局 | posterior、joint law 与有限积分／partial-trajectory bridge；在原 prefix 解析质量非零时，S088 `conditionalTailKernel` 的任意有限 tail 边缘已有直接等式；零质量明确返回 `none` | 原子表扫描加后续执行成本；一般 regular conditional distribution 及零质量版本仍属分析语义 |
| A05 | `FiniteObservation` 在绝对时钟执行结果上做 coordinate、tail reindex、fresh restart 和 splice | 所有给定 horizon 的 prefix/coordinate/restart/splice 等式；S089 的 kernel pointwise finite marginal 及 S096/S097 原 tail event/state Measure 的每个有限边缘均已直连；绝对续局与时间零 restart 分开 | 确定性 reindex 对结果原子表线性；完整 infinite tail `Measure`/kernel 仍需分析构造 |
| A06 | `abstractLaw.bind (realizationLaw time prefix)`，再把具体 dependent action 记录为 bundle 并编译成 event policy | bundle law 等于分析 `realizedKernel`；编译策略在终点与非终点均由局部有限 Dirac 表示实现 | 一步为抽象支持与 realization 支持的乘积；有限输出不推出对历史输入自动可测 |
| A07 | 从原 observed player/chance `FiniteLaw` 直接构造 terminal-aware event policy，不经过任意核采样 | 局部 compiled-kernel 等式、任意 bounded event-prefix `partialTraj` 等式，以及 S126 原 state-path Measure 的逐 horizon 完整 state-prefix 边缘等式 | 前缀原子数最坏随分支乘法增长；一般非原子 chance kernel 保留分析语义 |
| A08 | `horizon ↦ FiniteLaw Prefix`，同时提供坐标律和 Boolean cylinder mass | 较长前缀截断与较短前缀按 `FiniteLaw.Equivalent` 一致；每个 horizon 等于分析 `partialTraj` | 每次查询有限终止，原子数可能指数增长；不提供任意 Borel 事件 oracle |
| A09 | 执行到统一正支持终止界，把每个 event prefix 重放成终点吸收的 `ℕ → PathEvent`；`stateLaw` 再显式逐坐标投影为 `ℕ → State` | 所有 post-start finite event/state prefix 与坐标查询同继续执行一致；event 版另逐有限边缘对接分析 `partialTraj`，并证明正支持合法、终止、吸收 | 重放及状态投影对最终原子表线性；未证明两个 infinite-path `Measure` 整体相等 |
| A10 | 从任意绝对 prefix 计算 stopped center、unfinished mass、`B·q_H` radius；用有限预算或 `Nat.find` 搜索首个／最小 horizon | sound、minimal、`none ↔` 预算内全部失败；state policy 与 action-recording event policy 的 center/radius/interval 一致 | 搜索最多检查预算个 radius；要连接原 eventual utility 仍需终点一致、收益界和趋零证明 |
| A11--A13 | 正概率图先判定能否到终点，剪去不可达区，再以 Cramer 法解有理 Bellman 系统 | 行列式非零、唯一解、逐终点概率、`FiniteLaw (Option Terminal)`、zero-on-nonhit reward、first-hit 级数、`lateHitMass → 0` 与余项界 | 当前 Cramer 实现最坏需要阶乘级行列式算术；闭非终止类被显式保留，不要求全链吸收 |
| A14 | 在 coherent state/event prefix law 上用 `expectRat` 精确求有理 observable | 较早 cylinder observable 提升到任意较晚 horizon 后期望不变；event-to-state 投影与 state executor 一致 | 对当期有限原子表线性；不计算任意实值路径积分 |
| A15 | 每个 horizon 给可执行有理 observable 与 `ℚ≥0` radius；计算 center、scheme interval 并搜索容差 | 搜索 sound/minimal/none-iff、显式存在的 least horizon、零半径 cylinder coherence、state/event 投影；语义叶由 finite-marginal equality 与 pointwise uniform certificate 推出真实积分 enclosure 和搜索误差 | 算法不读 target expectation；任意 measurable/integrable utility 不会自动提供 approximant、measurability 或误差模数；当前语义证书为 state path 的 uniform 版本 |
| A16 | 一般 state/event effective path wrapper 在 reward 的绝对时刻 `start+k` 取值、折扣指数从 supplied start 归一为 `γ^k`，精确求前 H 项并把几何 radius 接入 A15 搜索；有限有理 chain 另以 Cramer 法精确解 `(I-γQ)v=r` | 一般 wrapper 证明 radius vanishes、每个正有理容差存在最小时界及 state→event estimate/interval 保持；有限链证明可逆、Bellman sound/unique、unroll 与同一尾界 | wrapper center 成本为 `H ×` 前缀原子数，prefix law 仍可能指数增长；chain 的 `r` 只属于 transient states，命中原 terminal 后 reward 为零；有限链不要求吸收；具体无限折扣积分仍需满足 A15 uniform certificate |
| A17 | `all` 用 `Finset.univ.filter` 无重复枚举；`find` 用显式 `FinEnum` 顺序执行 first-match | check 与原 root-bound pure Nash 等价；membership、soundness、failure iff absence、completeness | profile 数是各玩家纯策略数乘积，每次检查枚举单边偏离并执行有限博弈；不推出 mixed Nash |
| A18a | 把 chain 与 `Fin q` 确定性终止时 monitor 作 `Fin (n*q)` product；初始标签只消费一次，之后消费目标状态标签 | encode/decode、行归一、正系数更新、checked outcome-law 与 acceptance value、Bellman 聚合、accepted first-hit/late 分解 | product 求解维数为 `n*q`；`none` 显式保留闭非终止类质量；这里只是有限词终止接受，不是 Büchi/parity |
| A18b | 把原 terminal 变成永久自环，在 `n+m` 总状态的正支持图上自动判定 reachability、SCC、bottom 与 min-priority 偶数接受，再把 accepting/rejecting BSCC 约化为两终点链并以 Cramer 法求解 | 每个状态可达 bottom SCC、约化链 `autoCheck`、`I-Q` 行列式非零、Bellman sound/unique、接受／拒绝质量均在 `[0,1]` 且和为 `1`，且分别等于归约链的 `terminalProbability 0/1` | 闭集 reachability 实现为指数级，当前 Leibniz/Cramer 算术最坏阶乘级；原总链几乎必然进入底 SCC、底 SCC 内状态无限常返及 Measure 上 ω-event 等式仍需语义证明；约定仅为 min-parity |
| A19 | `RatEnclosure`／`RatOracle` 实现精确有理 enclosure；`SimpleObservable` 以常量、事件指标、加法和有理缩放组成；`EffectiveLaw.map/bind` 与 `EffectiveKernel.comp` 通过可执行逆像和 observable pullback 组合；uniform backend 对有理区间并事件给出精确 singleton enclosure | proof-only `Denotes`／`Represents` 关系证明 simple-observable expectation 包含真实积分，map/bind/kernel composition 保持原 Measure／Kernel 语义；EFG bridge 将有效 pushforward 连到 S082/S085/S086，并在 observable 精确表示玩家 utility 时将 oracle 连到 S101 | oracle 查询及语法树遍历有限终止；具体复杂度由事件 backend 与语法大小决定。事件语言必须对所需 preimage/pullback 封闭；任意可测集、任意可积函数、自动误差模数和零质量 RCD 版本不在算法契约内 |
| A20 | effective presentation/profile 显式携带 information、有限抽象律、prefix-dependent realization、终点判定、chance classifier/law，再复用 A06/A08 | raw compiled policy 的 analytic realization、所有 finite event/state-prefix 边缘、真实 chance prefix，以及 S092--S094 continuation/fresh restart 和 S134 normalized continuation 的逐 horizon 等式 | 当前高层直桥覆盖 discrete complete-history model；fresh restart 与绝对时钟续局保持为不同对象；任意 measurable model 需额外 arena/measurable 同构运输 |

### 5.1 有限 Markov 的首达、非终止与折扣约定

- `outcomeLaw : FiniteLaw (Option Terminal)` 中 `some a` 是最终首次命中终点 `a`，
  `none` 是永不命中任何终点的概率质量。
- `lateHitMass H = (Q^H p)_i` 是时刻 `H` 尚未命中但未来最终会命中的质量。进入永久
  非终止闭类的质量不计入它，所以即使 `none` 质量为正，`lateHitMass H` 仍趋于 0。
- `finiteDiscountedValue` 累加时刻 `0,...,H-1` 的 reward，因此尾界指数是 `γ^H`。
  若改用包含时刻 `H` 的截断约定，指数会相应平移；接口文档不得混用两种约定。

### 5.2 仍需按顺序闭合的项目

1. A15 的 state-path uniform certificate 已闭合；后续仅在真实消费者需要时增加 event
   path 或 `L¹` 版本，不能把 target expectation 当作算法输入。
2. S091 的 eventual-utility 直桥仍需终点一致与几乎必达到可算尾界的证明；
   S092--S094 的命名 finite-marginal bridge 已闭合，但不能误报为完整路径 `Measure`
   等式。
3. A19 的事件／observable 语言、enclosure、pushforward、bind、kernel composition 和首个
   非原子 backend 已闭合。后续扩展只能增加有明确闭包和误差契约的 backend；任意
   `Set`、任意 `Measure`、任意可积实函数或零测前缀 RCD 不构成可执行接口。
