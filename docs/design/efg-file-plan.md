# 整个 EFG 的文件规划

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

日期：2026-09-04。状态：45 个主库计算／语义落点均已建立；A19 另有纯运行与分析解释
两个导航聚合模块，
消费者迁移分阶段继续。

本规划覆盖 EFG 全部结构、执行、策略、均衡、表示、编译与验证文件。
它以现有架构为基础，将已验证的通用计算从示例中提取，并为主库分析声明安排计算对应物。
下文逐项标明已建阶段；示例消费者迁移不属于当前主库架构阶段。

当前工作树快照包含 EFG 主目录 182 个 Lean 文件（其中 `Simulation/` 42 个）、
直接配套模块 36 个，合计 218 个主库范围文件；EFG 示例另有 69 个。
[逐文件清单](efg-file-plan-inventory.md)列出这些文件的具体处理方式。
这些数量用于界定此次规划范围；后续模块状态以
[生命周期登记](efg-module-status.md)、Lean 源码及治理检查器为准。

## 1. 组织原则与实施边界

- 结构主干保持 `Arena → ControlledGame → ControlledDecisionGame → ControlledObservedGame`。
  可计算性要求放在具体操作上，不给所有 EFG 强加有限性、有理概率、可判定性或可测性。
- 通用概率算法归入 `Math/Probability/`；依赖历史、策略或续局的算法归入 EFG。
- 对有效输入可以直接计算的对象，算法定义是该实例的主运行表示；不得先构造
  `Measure`、无限路径或积分再投影出同一个有限结果。一般载体和分析定理的定义域
  不因此缩小，也不要求每个一般实例都具有有限表示。
- 有限精确计算、无限离散路径、非原子分析语义保留各自的输入契约，通过等式定理衔接。
- 这些等式属于[语义兼容层](efg-semantic-compatibility.md)：算法拥有计算值，分析定义
  保留一般数学语义；后者不因有效子域已有算法而称为 legacy。
- 整体采用两轨表示：可计算轨处理有效执行和数值，分析轨处理无法忠实算法化的一般
  对象；结构、历史、信息、策略和表示无关定理保持共用，不复制成两套理论。
- 每项迁移同时处理定义、证明、实际消费者和回归。原有构造的结论不能改成调用方提供的答案。
- 历史端点策略、发生位置策略、指定续局根、合法子博弈根保留各自语义。
- `Simulation/` 的现有分析实现路径保持原位。新增叶文件须有独立职责与依赖边界；
  不因目录名称或文件行数机械搬迁全部实现。
- 现行 [API 增长政策](efg-minimal-core-freeze.md)仍然有效。A19 的七个实现／语义 leaves
  按内部模块登记；2026-09-04 A19 架构决策所记录的唯一公共路径变化，是把纯 `Effective` 与 opt-in
  `Effective.Analytic` 两个零声明导航聚合加入 baseline，声明 ceiling 不变。其他公共
  晋升仍须单独评审。这不影响现在完成整份文件规划。

## 2. 总体文件布局

以下路径相对仓库根目录；列出的 45 个计算／语义落点现均已存在。
省略的逐个文件全部列在[清单](efg-file-plan-inventory.md)中。

`GameForm/` 保持 `Basic`、`Law`、`Continuation/{Core,Simulation,Iso}`、
`IndexedContinuation` 和历史 `LimitSPE` 的职责。
树前端保留 `GameTree`、`StochasticGameTree`、`ImperfectInformation`、
`BackwardInduction`、`FiniteArenaExtraction`、`Zermelo`、`ZeroSumGameTreeWithChance`。
`Strategy`、`Subgame`、`GameTreeNE`、`GameTreeSPE`、`GameTreeStrategicForm`
及端点编译器保留历史语义和已有消费者；不宣称与发生位置语义等价。

## 3. 主库落点及迁移来源

这是 45 个已经建立的具体实现／语义落点。A19 的 `Effective.lean` 与
`Effective/Analytic.lean` 是分别服务纯运行和分析解释的导航聚合，不计作算法或证明
owner。所有原定义在消费者迁移完成前继续可用；
若迁移导致命名或签名改变，必须记录精确对应关系，不添加空壳占位文件。
`Math/...` 均指 `EconCSLib/Math/...`，EFG 路径均指 `EconCSLib/GameTheory/ExtensiveGame/...`。

与[算法实现台账](efg-algorithm-implementation-ledger.md)的主要对应如下；一个算法项可以有
纯运行 owner、分析正确性叶和既有消费者桥三个不同落点。

| 台账项 | 本规划中的主要 owner |
|---|---|
| A06 | `Execution/Discrete/RealizedInformation.lean`；`Simulation/Kernel/FiniteRealizedInformation.lean` |
| A07 | `Execution/Discrete/ObservedChance.lean`；`Simulation/Presentation/Chance/FiniteExecution.lean` |
| A08 | `Execution/Discrete/EffectivePathLaw.lean`；`Simulation/Kernel/EffectivePathLaw.lean` |
| A09 | `Execution/Discrete/FiniteCompleteEventPath.lean`；`Simulation/Kernel/FiniteCompleteEventPath.lean` |
| A10 | `Execution/Truncation.lean`；`Execution/Discrete/ContinuationTruncation.lean`；`Simulation/Equilibrium/FinitePayoff.lean` |
| A11–A13 | `Math/Probability/FiniteMarkovChain/Reachability.lean`；`ReachabilitySemantics.lean` |
| A14 | `Execution/Discrete/EffectivePathUtility.lean` |
| A15 | `Execution/Discrete/CertifiedPathApproximation.lean`；`Simulation/Kernel/CertifiedPathApproximation.lean` |
| A16 | `Execution/Discrete/DiscountedPathUtility.lean`；`Math/Probability/FiniteMarkovChain/Discounted.lean` |
| A17 | `Observed/FinitePureNash.lean` |
| A18 | `Math/Probability/FiniteMarkovChain/Automaton.lean`；`Parity.lean` |
| A19 | `Math/Probability/Effective/{Enclosure,Core,Uniform}.lean`；`Effective/{Semantics,UniformSemantics}.lean`；`Simulation/Equilibrium/EffectivePathUtility.lean` |
| A20 | `Execution/Discrete/EffectiveKernelBehavioralProfile.lean`；`Simulation/Presentation/Kernel/EffectiveBehavioralProfile.lean`，并复用 `Simulation/Restart/Observed.lean` 的有限边缘桥 |

| 主库文件 | 来源与内容 | 语义验收要求 |
|---|---|---|
| `Math/Probability/FiniteLaw/Measure.lean`（已建） | 通用有限 Dirac 测度／积分定理；纯计算聚合不导入该分析叶 | 保留可测性、单点可测等局部条件；有限律的语义等价不要求原子列表相等；不新增返回 `Measure` 的数据定义 |
| `Math/Probability/FiniteMarkovChain.lean`（已建） | 通用有限有理链、有限迭代、线性求解、`autoCheck`、`autoSolve` | 实际构造检查结果和有理解；保留失败返回及瞬态／终态区分；不导入测度或积分 |
| `Math/Probability/FiniteMarkovChain/Semantics.lean`（已建） | 自动检查的吸收语义和求解器的首达积分正确性 | 保留全瞬态吸收等价、首达奖励与时间积分；不推广为任意历史依赖 EFG 求解器 |
| `Math/Probability/FiniteMarkovChain/Reachability.lean`（已建） | 以有限步可达分类剪枝瞬态矩阵，再用 Cramer 法精确求解有理 Bellman 系统；计算总首达、逐终点、非终止概率、零收益值、截断余量及可验证 `outcomeLaw?` | 对任意有限有理链保留闭合非终止类并显式给出其质量，不再要求全局吸收；语义正确性由独立叶证明；不把历史依赖 EFG 自动压缩为有限 Markov 状态，也不处理一般实数或不可数链 |
| `Math/Probability/FiniteMarkovChain/ReachabilitySemantics.lean`（已建） | 证明剪枝链自动通过吸收检查、Bellman 矩阵非奇异、解唯一且概率非负，并给出逐终点首达、非终止质量、`outcomeLaw?` 成功、有限时界分解及 `lateHitMass → 0` | 计算向量与原有限链首达语义精确一致，闭合非终止类由结果载体内层 `none` 的质量表示；保持为分析正确性叶，不声称任意 EFG、无限状态链或任意路径事件可算法化 |
| `Math/Probability/FiniteMarkovChain/Discounted.lean`（已建） | 对任意有限有理转移链检查 `0 ≤ γ < 1`，对瞬态 reward `r : Fin n → ℚ` 用 Cramer 法解 `(I - γQ)v = r`，并计算有限展开与几何余项界；命中终点后 reward 为零 | 闭合非终止类在严格折扣下仍可处理；非奇异性、Bellman 唯一性和余项界均已证明。当前 `n × n` 密集有理求解使用 Leibniz 行列式／Cramer，系数运算最坏为阶乘量级，另有有理数位长成本；不声称终点持续回报、一般实折扣、平均回报或未给有限状态表示的 EFG 可直接求解 |
| `Math/Probability/FiniteMarkovChain/Automaton.lean`（已建） | 将有限有理链与确定性有限终止时 monitor 作乘积，再复用 reachability 求解器计算接受终点值及非终止质量 | 初始标签只消费一次，每步转移保留确定 monitor fold；接受值的首达概率解释须实例化通用 reachability 语义，并保留显式 weight-valid／Bellman correctness 前提。对 `n` 个瞬态、`m` 个终态和 `q` 个 monitor 状态，乘积规模为 `nq`/`mq`，密集 Cramer 求解维度为 `nq`且现有行列式实现最坏为阶乘量级；这是有限词的终止时 DFA 检查，不是 Büchi/parity 或底 SCC 无限监视算法 |
| `Math/Probability/FiniteMarkovChain/Parity.lean`（已建） | 把原终态扩展为概率一自环，在全部 `n + m` 状态上计算正支持图、可达性、SCC、底 SCC 和最小 priority 偶性，再总是构造接受／拒绝底类约化并解出有理 Bellman 系统 | `solveParity` 对每个规范化有限有理链都返回总的精确有理解；非奇异性、方程、`[0,1]` 范围和接受／拒绝互补均已证明，并且接受／拒绝向量分别等于两终点归约链的 `terminalProbability 0/1`。已实现的约定严格是 **min-parity**；不把 max-parity 或未实现的 priority 转换 API 记为已有。单次 least-closed-set reachability Boolean 判定在朴素 `Finset` membership 成本模型下最坏为 `O(2^N N^3)`（`N = n + m`），这不是整个 solver 的复杂度；后续 `N × N` 密集有理 Leibniz 行列式／Cramer 计算最坏为阶乘量级并另有有理位长增长。原总链几乎必然进入底 SCC、底 SCC 内优先级无限常返以及分析路径测度上的 ω-event 等式仍待独立语义桥 |
| `Math/Probability/RationalIntervalUnion.lean`（已建） | 纯有理端点、裁剪、交集及有限并集容斥概率算法 | 同一有限描述的精确集合并语义；包含重复、相交、裁剪、反向与单点；不依赖实数测度 |
| `Math/Probability/RationalIntervalUnion/Volume.lean`（已建） | 有理区间事件及其单位区间体积解释 | 精确概率属于 `[0,1]`；一般非原子测度仍是分析对象，任意实数事件不被声称可判定 |
| `Math/Probability/Effective/Enclosure.lean`（已建） | 以精确有理闭区间回答任意正有理 tolerance 查询，并提供加法、减法、缩放的可执行 enclosure 算术 | 运行层只保证区间宽度；它不读取真实值，真实概率／积分属于区间由独立 `Represents` 证书证明 |
| `Math/Probability/Effective/Core.lean`（已建） | 以模型选定的事件码、有限有理 simple observable、逆像编译器及 expectation-transformer kernel 组成有效 law/map/kernel 接口 | pushforward、law bind 与 kernel composition 均为结构性算法；事件语言必须对实际使用的逆像和 observable pullback 封闭，不接受任意 `Set` |
| `Math/Probability/Effective/Uniform.lean`（已建） | 有理区间有限并事件的精确非原子单位区间 backend；事件质量复用容斥算法并返回 singleton enclosure | 展示非原子概率可在选定事件语言上精确计算；不扩展为任意实端点、任意可测集或任意数值积分 |
| `Math/Probability/Effective/Semantics.lean`（已建） | 用 proof-only `Denotes`／`Represents` 关系解释事件、simple observable、law、map 与 kernel，并证明 expectation enclosure、pushforward、bind 和 composition 正确 | 语义证书不进入运行数据；调用者必须证明事件可测、observable 表示及相应 law/kernel representation；一般分析对象不会自动生成有效代码 |
| `Math/Probability/Effective/UniformSemantics.lean`（已建） | 将 uniform backend 的事件质量和 simple-observable expectation 识别为单位区间 volume，并解释常值非原子 kernel | correctness 只覆盖有限有理区间并事件语言及其有限有理 simple observables；不声称任意 Borel event oracle |
| `Execution/Discrete/HistoryKernel.lean`（已建） | 通用前缀策略、动作选择、状态／事件一步律与有限迭代；不依赖示例 | 任意有效前缀、绝对时钟、依赖动作纤维及终止吸收；终点动作返回 `none`；已证明事件记录投影及 Markov 策略接入 |
| `Execution/Discrete/FiniteObservation.lean`（已建） | 有限状态／事件前缀的坐标边缘、尾部重索引、时间零重启和绝对前缀拼接 | 绝对续局保留原时钟；fresh restart 只从最新状态以时间零执行；拼接丢弃重复的 fresh 零坐标；时界在旧前缀内时精确截断且不执行随机步 |
| `Execution/Discrete/ObservedChance.lean`（已建） | 从原玩家 behavioral `FiniteLaw` 与机会 `FiniteLaw` 直接组装事件历史策略；确定性追加历史，并用显式终止判定执行任意有界前缀 | 玩家／机会分支逐点保留原动作律，终点精确返回 `none`，完整动作事件与绝对时钟不丢失；运行接口不接收 `Measure`、可测核或 realization presentation，一般非原子机会表示仍留在分析轨 |
| `Execution/Discrete/RealizedInformation.lean`（已建） | 以 `FiniteLaw.bind` 组合有限抽象动作律和依赖当前状态动作纤维的有限实现律，再 `map` 为动作 bundle 并编译到事件历史执行器 | 结果类型保证具体动作属于当前状态，`Option` 明确区分终点 killed 分支，编译律由原两阶段有限选择构造；不从任意有限律值函数推导输入可测性，一般分析 realization kernel 仍单独保留 |
| `Execution/Discrete/EffectivePathLaw.lean`（已建） | 对每个步数复用 `prefixLawFrom` 计算精确状态／事件 `FiniteLaw`，提供坐标律和 Boolean 柱事件有理质量 | 零时界正确，较长前缀截断后与较短前缀按 `FiniteLaw.Equivalent` 同义，坐标及柱质量随扩展不变；保留所给前缀与绝对时钟；不构造无限路径、`Measure` 或任意集合查询，输出原子数可随分支和时界指数增长 |
| `Execution/Discrete/EffectivePathUtility.lean`（已建） | 直接在投影一致的状态／事件前缀律上用 `FiniteLaw.expectRat` 计算有理可观测量，并证明柱可观测量的时界不变性及事件到状态投影 | 对已给原子表的期望计算是线性遍历；构造该表仍有执行树的指数最坏增长。只给有限前缀效用；不自动获得一般无限路径效用或实积分 |
| `Execution/Discrete/CertifiedPathApproximation.lean`（已建） | 用可计算的有理前缀可观测量和非负有理 radius 生成精确 center、scheme interval、预算内首个时界及显式存在证明下的最小时界 | 预算搜索最多比较 `budget` 个 radius，且只在选中时界计算 center；center 对原子表线性，前缀律构造仍可指数增长。**scheme interval 不等于目标积分误差界**；须另有语义证书才能声称外部目标落在区间内 |
| `Execution/Discrete/DiscountedPathUtility.lean`（已建） | 对绝对时间索引的状态／事件有理逐期 reward，在非负有理 `γ < 1` 下读取绝对时刻 `start + k` 的 reward，并以从所给起点重新归一的 `γ^k`（`0 ≤ k < H`）计算前 `H` 项 observable 和 center；显式统一界 `B` 给出 `B * γ^H / (1 - γ)` 几何 radius | 已证明 radius 趋零，因而每个正有理容差都有可搜索时界；复用 A15 的预算／最小时界搜索及 state→event 投影。已给 horizon 律的 center 计算对 `H × 原子发生数` 线性，前缀律生成可随分支指数增长；该纯层的几何 radius 仍只是 scheme 数据，须独立语义证书才能包络某个无限折扣路径积分 |
| `Execution/Discrete/ContinuationTruncation.lean`（已建） | 从任意绝对状态／事件前缀计算未终止质量、停止收益 center、`bound * unfinishedMass` radius、预算内首个时界和显式存在证明下的最小时界 | 保留旧前缀、动作发生位置及绝对时钟；预算搜索最多试行指定数目的有限执行，每个前缀律可随分支与时界指数增长。与原续局积分的误差结论仍需分析 realization、效用因子分解、有界性及终止一致证书 |
| `Execution/Discrete/FiniteCompleteEventPath.lean`（已建） | 把有界事件前缀律映射为终点后吸收的按需完整事件路径律，保留绝对坐标和所有动作发生位置 | 正权重支持终止证书用于证明合法、终止和任意时界前缀／坐标一致，不参与运行时构造。对已给有限原子表的路径映射是线性的，有界执行本身可指数增长；这些函数值原子仍不是一般无限路径 `Measure` |
| `Execution/Discrete/EffectiveKernelBehavioralProfile.lean`（已建） | 以有限抽象动作律、依赖前缀的有限 realization 律、可判定终点／机会角色及固定机会律装配可执行 profile，再编译为事件历史执行与 coherent 前缀律 | 保留原两阶段信息动作／具体动作语义，机会前缀的实现律必须精确等于固定机会律。有限 `bind` 支持可相乘，多步执行可指数增长；这只是有效离散模型，不从逐点有限性推出一般载体上的可测性 |
| `Execution/FinitePayoff.lean`（已建） | 通用化有限有理期望和停止收益；覆盖确定转移 Arena 历史以及随机转移 KernelArena 状态／事件前缀 | 完整历史、动作事件及原终止测试均保留；未终止结果仍为零；事件遗忘动作后的状态收益期望已证明不变 |
| `Execution/FiniteCompletePath.lean`（已建） | 通用化有界终止下的历史回放与有限完整路径律，并下移纯合法吸收转移谓词 | 构造只需有限执行；仅在正权重支持终止条件下证明合法吸收与全坐标边缘一致；保留初始前缀长度和动作历史 |
| `Execution/Truncation.lean`（已建） | 通用有限截断估计、预算搜索及在显式存在证明下的最小自然数搜索 | 精确有理中心和半径；预算耗尽返回 `none`；零容差不被几乎必终止条件冒充为有限可达；分析层可单独提供存在证明 |
| `Execution/Discrete/ConditionalContinuation.lean`（已建） | 通用有限条件律、联合执行、Bayes 条件期望，以及 Arena 和 KernelArena 前缀续局 | 先验覆盖所有相容历史；零概率观测返回 `none`；状态和动作事件续局均保留完整前缀与绝对时钟 |
| `Observed/FinitePureNash.lean`（已建） | 通用根绑定纯策略战略形、精确有限时界停止收益、Boolean Nash 检查、无重复全枚举及首个解搜索 | `all` 只需原纯 profile 空间的 `Fintype`；确定顺序的 `find` 显式要求 `FinEnum`。检查一个 profile 枚举全部玩家及其单方策略，全搜索再乘以 profile 数；保持有限窗口收益，不代称最终效用或一般纯 Nash 存在性 |
| `Simulation/Kernel/FiniteExecution.lean`（已建） | 状态／事件前缀重索引、局部分析实现条件，以及状态／带动作事件的一步、任意有限步前缀和指定坐标边缘等式 | 等式由局部动作核表示和步数归纳推出；接受任意初始前缀并保留绝对时钟；事件坐标的状态投影也与分析边缘一致；不把目标边缘等式作为输入 |
| `Simulation/Kernel/EffectivePathLaw.lean`（已建） | 复用有限执行对应定理，将有效状态／事件路径律的每个所求时界解释为 weighted-Dirac 前缀测度，并将任意有限重编号事件尾部及其状态投影连到原 tail laws | 从任意给定前缀和根出发的前缀都精确等于原 `Kernel.partialTraj`；尾部定理对每个有限 horizon 等于 `tailEventPathMeasureFromPrefix`/`tailStatePathMeasureFromPrefix` 的 `frestrictLe` 边缘。它们不构造无限路径测度，也不把任意可测路径事件变成算法查询 |
| `Simulation/Kernel/CertifiedPathApproximation.lean`（已建） | 在有效状态前缀律与分析无限状态路径律的每个所需有限边缘一致时，把有理 center 识别为 lifted prefix observable 的积分，再用真实路径效用的统一逐点 radius 证书推出积分区间和成功搜索的误差界 | 分析路径测度、外部实值效用、可测／可积证明、lifted observable 可测性及逐点统一误差界都是 theorem-only 证据，不进入纯搜索。该叶使 A15 的 scheme interval 在这些显式前提下成为真实目标积分证书；它不使任意 scheme 自动正确、不构造无限 `Measure`，也没有额外运行时复杂度 |
| `Simulation/Kernel/FiniteRealizedInformation.lean`（已建） | 在局部抽象核为有限律推前、具体 realization 核为 weighted-Dirac 有限律的条件下，用 `measure_bind`／`measure_map` 解释两阶段执行 | 证明分析 `realizedKernel` 与可执行 bundle 律逐点相等，并覆盖终点 killed 质量后得到事件策略实现；不从一般有限输出自动制造可测核，任意不可数历史上的可测依赖仍属分析边界 |
| `Simulation/Kernel/FiniteCompleteEventPath.lean`（已建） | 将有界完整事件路径律解释为有限 weighted-Dirac 测度，证明所有后续前缀以及事件／状态坐标边缘等于原 `partialTraj` | 等式对超过终止 bound 的查询仍成立；分析策略、局部 realization 和终止证书都是显式输入。**逐时界有限边缘的正确性不等于已构造一般整体无限路径 `Measure`** |
| `Simulation/Presentation/Chance/FiniteExecution.lean`（已建） | 以表示证书证明原 compiled analytic policy 逐点等于直接玩家／机会有限事件策略，再由通用有限执行桥提升到任意有界事件前缀及完整状态前缀 | 非终点和终点 optional action law 均精确对应，weighted-Dirac `finitePrefixLawFrom` 等于原 `partialTraj`；只在完整事件执行后 map states，得到原 `statePathMeasure` 的任意 `frestrictLe` 边缘。执行器不求值 realization kernel，一般可测或非原子 presentation 继续保留分析语义 |
| `Simulation/Presentation/Kernel/EffectiveBehavioralProfile.lean`（已建） | 用可测等价、抽象动作律和具体 realization 律的局部 weighted-Dirac 表示证书，把有效 profile 编译到原 `KernelBehavioralProfile.compiledPolicy` | 这是有效离散模型到原分析模型的精确桥：编译策略逐点相等，每个有限事件前缀测度等于 `partialTraj`；对原高层 profile，先完整执行事件前缀再 map states，精确得到 `statePathMeasure` 的任意有限 `frestrictLe` 边缘。它不从逐点有限支持推出可测性，也不制造整体无限路径测度 |
| `Simulation/Continuation/FiniteConditioning.lean`（已建） | 有限 posterior 续局的 Dirac 测度解释、`partialTraj` 等式及绝对路径续局的有限边缘等式 | 零质量观测仍由可执行层返回 `none`；不引入零测前缀上的正则条件分布版本；有限 posterior 先重索引到现有可测前缀空间再做 measure bind |
| `Simulation/Equilibrium/FinitePayoff.lean`（已建） | Arena 有限历史收益的 Dirac／所给完整路径坐标积分等式，分析未完成质量与可执行 `unfinishedMass` 的等式，`bound * unfinishedMass` 截断误差界，以及 KernelArena 状态／事件前缀收益的 `partialTraj` 积分等式 | 计算定义仍返回精确有理数；分析文件只添加等式与误差定理；所给完整路径律必须带有限边缘一致证书；目标函数的可积性、有界性及已终止路径上的收益一致是显式前提 |
| `Simulation/Equilibrium/EffectivePathUtility.lean`（已建） | 对表示原 profile state-path Measure 的有效 law 计算有限有理 simple observable 的 expectation oracle | 调用者给出 simple observable `Denotes` 原玩家 utility 的证书后，证明 oracle 表示原 `PathUtility.expectedUtility`；一般可积 utility 不自动具有有限表示或有效误差模数 |
| `Simulation/Restart/FiniteExecution.lean`（已建） | 时间零 fresh restart、保留绝对时钟的续局及 fresh 拼接前缀的有限 Dirac 语义 | 对任意 horizon 直接证明等于原 restart 测度；旧前缀内是纯截断，旧前缀后分别按绝对或 fresh 时钟执行；不把两种时钟自动等同 |

`HistoryKernel.lean` 已在主库中完成任意有限律的一步和多步执行，
不依赖两个具体历史核示例；`FiniteExecution.lean` 已证明局部可测实现下的
状态／事件一步及任意有限步前缀分析对应。示例消费者迁移不属于当前主库架构阶段。
`FiniteObservation.lean` 在同一执行器上构造坐标律、尾部律和任意绝对时界的前缀律，
并把保留绝对时钟的续局与从时间零重启后拼接的续局分为两个定义。
`FiniteConditioning.lean` 已把有限 Bayes posterior 续局解释为同一
`partialTraj` 的 measure bind，并证明它等于现有绝对路径续局的
指定有限前缀边缘。这一桥接不为零质量前缀选择正则条件分布。
`Simulation/Equilibrium/FinitePayoff.lean` 已证明精确有理收益计算等于
有限 Dirac 解释、与有限边缘一致的所给完整路径坐标积分，
以及状态／动作事件 `partialTraj` 积分；它还证明分析未完成质量
等于可执行 `unfinishedMass`，并用它证明计算截断半径的积分误差界。
它不把数值定义改为积分。
`FiniteCompletePath.lean` 已把有界终止的有限历史律构造成按需坐标计算的吸收路径律；
终止证据只用于证明正权重路径合法、终止及边缘一致，不用于伪造终止算法。
`FiniteCompleteEventPath.lean` 对事件前缀做同样的有界回放，并保留动作发生位置。
它的分析叶证明所有有限边缘等式；一族正确的有限边缘本身不构成对任意
无限路径事件的可查询 `Measure`。纯 `CertifiedPathApproximation.lean` 的 radius 只是方案数据；
`Simulation/Kernel/CertifiedPathApproximation.lean` 另要求分析路径律的有限边缘一致、
外部效用可测可积、lifted observable 可测及真实逐点统一误差证书，才把 center／radius
提升为目标积分包络和成功搜索的真实误差界。这些 theorem-only 证据不进入运行算法。
`DiscountedPathUtility.lean` 使这个方案的 observable、几何 radius 和正容差时界存在性变得可计算，
但调用者仍须证明其无限折扣效用满足上述分析证书；当前文件没有自动构造该外部效用或路径测度。
终止点的动作层必须能表达零质量，例如用 `Option (FiniteLaw ...)` 表示无动作，
再证明其解释等于原 killed action kernel；后继状态／事件层则保留原吸收分支。
不能在空动作类型上伪造规范化 `FiniteLaw`，也不能混淆这两个终止约定。
有效 kernel profile 的运行主体只依赖有限抽象／实现／机会律；分析叶在显式局部
weighted-Dirac 与可测等价证书下才连到原 profile。这是离散模型桥，不是对一般
不可数信息空间的自动可测化。
有限链 `Automaton.lean` 只处理在终止时判定的有限词 DFA monitor；
`Parity.lean` 则面向无限运行的 min-parity 目标做底 SCC 分类与有理 Bellman 求解。
当前没有 max-parity API。Bellman 向量已经识别为两终点归约链的
`terminalProbability 0/1`；尚未证明原总链几乎必然进入底 SCC、底 SCC 中有关状态
几乎必然无限常返，也没有把结果识别为分析路径测度上的 ω-event。
单位区间体积算法具有指数最坏复杂度；第一阶段保留其精确结果，之后才能独立优化。

## 4. 原位调整的文件与消费者

| 现有位置 | 计划调整 |
|---|---|
| `Math/Probability/FiniteLaw/Conditioning.lean` | 接收有限条件续局原型中不依赖 EFG 的 Bayes 期望与联合条件化定理 |
| `Execution/StochasticExecution.lean` | 继续唯一拥有确定转移 Arena 的有限历史执行；接收有限计算需要的未终止质量辅助定义 |
| `Execution/InfiniteTrajectory.lean` | 复用前述有限辅助定义，保持旧名称可追踪；明确所给完整律接口与构造算法的区别 |
| `Execution/Discrete/KernelTrajectory.lean` | 现有状态策略作为历史策略特例，证明对应；避免复制有限迭代器 |
| `Simulation/Kernel/DiscreteBridge.lean` | 保留既有全路径一致性证明；新有限语义叶复用该证明，不建立第二套桥接 |
| `Simulation/Continuation/Conditioning.lean` | 保留原正质量分析条件核；已将有效 raw event policy 的任意有限 `tailPrefixLawFrom` Dirac 边缘精确连到 represented prefix 上的 `continuationTailKernel`，并在 singleton prefix 质量非零及 Standard Borel/单点可测条件下连到 RCD `conditionalTailKernel`。保留完整前缀与绝对时钟；零质量 prefix 版本选择和整体无限核等式仍属分析边界 |
| `Observed/Controlled/Law/Discrete.lean` | 将通用计算接入现有行为执行；法则仍由 executor 构造而非新增结果证书输入 |
| `Observed/Controlled/Law/DiscretePath.lean` | 接入有界终止的构造性完整路径特例；原一般所给路径律接口继续保留 |
| `Observed/Behavior.lean`、`Chance.lean`、`Mixed.lean`、`General.lean` | 复用同一有限概率与历史执行；分别保持行为／完整计划／行为计划上的分布语义 |
| `Observed/Controlled/Semantics.lean`、`Observed/SPE.lean` | 复用收益与策略评估；纯执行、合法根和 complete subgame coverage 条件保持显式 |
| `Simulation/Restart/` | 有限计算复用现有拼接、绝对时钟与信息重基证书。`Observed.lean` 已将 A20 在 discrete complete-history representation 下的每个有限 horizon 分别连到原绝对时钟 `continuationEventPathMeasure`、执行后投影的 `continuationStatePathMeasure`、时间零 `freshRestartStatePathMeasure`，以及 tail 坐标零 marker 规范化后的 `normalizedContinuationEventPathMeasure`。fresh restart 与绝对时钟续局保持为两种执行；不声称整体无限 `Measure` 可执行或零质量 RCD 等式 |
| `Compiler/`、`FOSG/Sequentialization/` | 消费通用有限执行与收益；分别验证严格／弱关系及宏微步概率保持 |
| `Relations/`、`Observed/*Morphism*`、`*Refinement*` | 在已有关系上增加所需计算对应证明；保持同构、细化、耦合及弱模拟强度 |
| `Math/Probability/PMF/` | 逐一检查尚存消费者，完成语义保持迁移后再评估删除；不删除仍服务一般 PMF 的定理 |

自动逼近的分析包装负责从几乎必达证明推出搜索内核所需的终止事实。
数值输入仍是原有效策略、有理收益／界和容差；不能要求调用方预先提供所求时域或期望。
有限计算入口不能经辅助定义反向导入 `Measure`、Bochner 积分或完整分析路径层。

## 5. 主库 58 个分析声明的文件级处理

该快照来自[逐声明分类](../../scripts/efg_computability_classification.json)。
下表覆盖全部 18 个原属文件；数量不是删除任务，计算对应物也不自动消除原分析声明。
路径均相对 EFG 主目录。
关于哪些能计算、需要哪些输入及不能声称哪些结论，参见
[严格可实现性分析](efg-library-computability.md)和[58 项逐项清单](efg-library-computability-declarations.md)。

| 原属文件 | 声明数 | 计算落点与保留边界 |
|---|---:|---|
| `Simulation/Kernel/Arena.lean` | 1 | 有限律的测度解释进入 `FiniteLaw/Measure`；任意非原子 arena 保留 |
| `Simulation/Kernel/Execution.lean` | 4 | `HistoryKernel` 与 `FiniteExecution`：有效动作／转移组合、终止分支 |
| `Simulation/Kernel/HistoryPath.lean` | 5 | 同上：任意有限前缀与历史依赖，完整分析路径仍保留 |
| `Simulation/Kernel/EventPath.lean` | 8 | 同上：动作记录、联合事件及状态投影；不把事件历史压缩为当前状态 |
| `Simulation/Kernel/RealizedInformation.lean` | 2 | 有效抽象动作映射及有限律 `map`；一般可测实现保留 |
| `Simulation/Kernel/StatePath.lean` | 1 | 有限边缘和有界终止路径接口；一般无限律不由有限步计算自动构造 |
| `Simulation/Presentation/Chance/Measurable.lean` | 3 | 有效机会律、可执行角色判断接入有限执行；任意可测模型保留 |
| `Simulation/Presentation/Chance/MeasurableHistory.lean` | 2 | 原有效终止／历史操作复用；一般测度推前保留分析解释 |
| `Simulation/Presentation/Chance/Realized.lean` | 1 | 复用有限动作实现等式；不可把所求实现律替换成外部给定结果 |
| `Simulation/Presentation/Kernel/Core.lean` | 3 | 有限有理 profile 的装配与核等式；一般核策略仍保留 |
| `Simulation/Continuation/Path.lean` | 3 | 完整前缀上的有限续局；一般续局路径律保留 |
| `Simulation/Continuation/Conditioning.lean` | 2 | `ConditionalContinuation`／`FiniteConditioning` 的正概率原子情形，以及有效 raw event policy 的任意有限 tail 边缘到原 `continuationTailKernel`、正质量原子上 RCD `conditionalTailKernel` 的等式；一般零质量 prefix 版本选择和正则条件分布保留 |
| `Simulation/Continuation/Observed.lean` | 5 | 有限续局收益及截断对应；指定根与新旧时钟约定保持 |
| `Simulation/Equilibrium/Outcome.lean` | 5 | 有限收益、吸收链特例和积分逼近；原始无限路径上全定义的效用不改成部分搜索 |
| `Simulation/Restart/Observed.lean` | 2 | A20 在 discrete complete-history representation 下已有绝对续局 event/state、时间零 fresh-restart state 及坐标零 marker 规范化的逐 horizon 有限边缘桥；两种时钟不混同，原整体无限重启测度和零质量 RCD 边界保留 |
| `Simulation/Restart/Trajectory.lean` | 4 | 有限拼接路径及边缘等式；一般完整路径推前保留 |
| `Observed/Controlled/Law/Analytic.lean` | 1 | 保持一般分析适配器；有限特例通过原一致性定理进入共同路径律载体 |

79 个示例分析声明继续参与完整审计。它们用于非原子、无限性及不同表示的边界证明，
不统一改成有限分布。EFG 的总任务也不局限于这 58 个主库分析声明：结构、编译器、
信息约束、获胜语义和全部消费者均在本规划的文件清单中。

## 6. 导入入口与示例安排

| 现有 `Interface/` 文件 | 最终负责的能力 |
|---|---|
| `StructuralCore.lean` | 窄结构入口，保持现有五模块边界 |
| `Core.lean` | 结构、历史、有限／回忆／子博弈证书和基础有限执行 |
| `Objective.lean` | 无概率的终端历史与完整路径目标 |
| `Winning.lean` | 逻辑获胜与决定性 |
| `Winning/Stochastic.lean` | 离散无限路径上的几乎必胜 |
| `Execution/Finite.lean` | 经审核的有限随机执行、有限收益与条件计算；保持无完整测度层 |
| `Execution/Infinite.lean` | 无限离散语义与完整路径特例；完整律的构造条件明确 |
| `Execution/Analytic.lean` | 一般可测执行与有限计算的分析对应定理 |
| `Relations/Discrete.lean` | 结构／离散概率关系 |
| `Preservation.lean` | 表示保持契约与对应定理 |
| `Equilibrium/Discrete.lean` | 纯／行为／混合语义，以及审核后的有限纯 Nash 检查 |
| `Equilibrium/Analytic.lean` | 一般测度策略、续局效用，以及有限／逼近／有效事件与 simple-observable 对应 |
| `Restart.lean` | 新时钟重启与原历史续局之间的条件化传输 |
| `Compilation/Discrete.lean` | 有限前端编译及 FOSG 序列化 |

`EconCSLib.lean` 保持经治理的精简入口。独立分析数学叶不加入纯 `FiniteLaw.lean` 聚合。
重启与编译是不同导入分支，互不依赖。任何导出变化都与闭包检查和生命周期登记一起实施。

所有 69 个示例保留为可运行消费者。8 个 `Finite*` 算法／语义原型以及两个历史核示例、
一个非原子示例按第 3 节提取通用部分；具体模型、反例、数值和 `#eval` 留在原文件。
`FiniteConditionalContinuation` 的通用 Bayes 定理单独下沉到数学层。
仓库中的其他 `Finite*` 示例仍是建模／编译回归，不按文件名前缀一律迁移。
现有 `ImportBoundary` 示例继续保护导入分层。

## 7. 实施顺序与验收文件

| 阶段 | 文件工作 | 完成条件 |
|---|---|---|
| P0 | 核实声明归属、消费者、生命周期与增长政策 | 已完成：规划、逐文件清单、声明分类与机器登记一致 |
| P1 | 数学解释层、有限收益、条件续局和计算辅助定义提取 | **主库架构已完成**：数学层不依赖 EFG，有限层不依赖分析层；示例消费者迁移另行处理 |
| P2 | `HistoryKernel` 通用化及 `FiniteExecution` 桥接 | **主库架构已完成**：任意有限律与有效初始前缀的状态／事件多步等式，以及历史、动作记录、绝对时钟和吸收回归均已建立；示例迁移另行处理 |
| P3 | 完整路径、吸收／折扣链、折扣路径方案、终止时 DFA、min-parity 底 SCC 与截断 | **已建当前主库落点**：原路径／积分等式、失败及误差语义均显式保留；无限折扣积分证书、max-parity API 及 parity 的分析 ω-event 对应尚待实现；示例迁移另行处理 |
| P4 | A19 有效事件／simple-observable 概率层、Nash、策略装配、续局、重启和编译消费者迁移 | 有效 law/map/kernel 组合、单位区间非原子 backend、S082/S085/S086/S101 语义桥、有限纯 Nash 和有效 kernel profile 均已建；任意可测集、任意可积函数与零测前缀 RCD 仍在分析层 |
| P5 | 接口导出、登记、审计和文档同步 | 45 个实现／语义落点及 A19 两个导航聚合的源文件已建；新增公共能力仍受 API 增长政策约束 |

验证沿用以下文件，按实际改动扩展有意义的检查，不自动重设基线：

- `scripts/check_efg_api_growth.py`、`scripts/efg_api_growth_baseline.json`：公共表面。
- `scripts/check_efg_governance.py`：依赖闭包、模块登记与职责边界。
- `scripts/check_efg_computability.py`、`scripts/efg_computability_classification.json`、
  `scripts/efg_computability_baseline.json`：可计算入口、全部原声明和语义分类。
- `scripts/check_efg_axioms.py`、`scripts/check_lean_placeholders.py`：证明依赖与占位符。
- `tests/FiniteLawSmoke.lean`、`tests/EffectiveProbabilitySmoke.lean`、已有 EFG
  `ImportBoundary` 示例及相应检查器测试。
- `docs/design/efg-module-status.md`、`efg-public-api.md`、`efg-semantic-universes.md`、
  `efg-computability-migration.md`、`efg-proof-audit.md`：迁移后按原权威分工同步。

Lean 实施阶段运行库／示例构建、占位符检查及三个架构／计算检查；
计算与证明边界变化时复核相应执行回归、Lean 内核检查和公理审计。
文档与治理更新至少核对清单覆盖、链接、治理与 diff；A19 的运行行为另由
`EffectiveProbabilitySmoke.lean` 保护。完整源码改动仍按上列构建与审计门执行。
