# EFG 主库不可计算声明的严格可实现性分析

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

本文的算法与分析定义按照
[语义兼容层规则](efg-semantic-compatibility.md)衔接。有限或其他有效输入优先调用
算法；一般 `Measure`、`Kernel`、无限路径和积分定义继续作为当前分析语义，不能仅因
存在一个有效子域算法而称为 legacy。只有命名的精确等式、误差界或几乎处处定理
才能把结论从计算层传到分析层。
作为算法博弈论库，对有效输入可直接计算的结果以算法对象作为该实例的主运行表示；
分析对象负责更一般的语义和正确性解释。一般载体、核、无限路径和定理定义域保持
不变；没有有效表示的实例不被排除，只是不声称具有统一的可执行求值器。
这形成两条表示轨：能忠实算法化的声明和消费者进入可计算轨，确实缺少有效表示的
对象保留在分析轨；二者共用 EFG 结构，并通过命名定理衔接。

复核日期：2026-09-04。范围是前述 EFG 审计中的 **58 个主库声明**，
分布于 18 个文件，不含 79 个示例声明，也不是对整个 EconCSLib 其他领域的审计。
逐项结论见[58 项清单](efg-library-computability-declarations.md)，
原签名、源码摘要和诊断保存在[分类记录](../../scripts/efg_computability_classification.json)。
在这些严格边界上进一步区分已有／待补的有限算法、无限时域算法、认证近似、
半判定与明确障碍，见[算法机会审计](efg-algorithm-opportunity-audit.md)。
当前完整 checker 另扫描 265 个模块，保留 137 个已分类 `noncomputable` identity，
分布在 35 个模块；新增七模块 `Effective` 家族使用 proof-only 语义关系，没有增加
`noncomputable` 数据声明。

**结论：这些声明不能统一视为数学上不可计算。很多有限操作已有可执行核心；
但本轮尚未验证任何一个能在原签名、原假设和全部输入语义下直接替换。**
18 个模块的副本去掉 `noncomputable` 后，58 个原声明各自产生编译错误。
这证明当前实现依赖不可编译的数据构造，不证明所有等价实现都不可能。
本轮没有改写这 58 个原分析声明或降低审计基线；除有限收益、完整路径重放、正质量
条件续局和截断搜索外，A19 已加入选定事件码／有限有理 simple-observable 子域的
有效 law/map/kernel 接口及真实非原子 backend。分析层以独立 representation 定理连接
原 Measure／Kernel／积分，没有把计算定义退化为积分或条件核。

## 1. “做成可计算的”必须分开判断

| 判定层次 | 验收条件 | 本轮结果 |
|---|---|---|
| 原函数体能否直接编译 | 只删修饰符，原签名和函数体不变 | 58 项均失败 |
| 同签名等价改写 | 可编译 `def`，且证明对原域全部输入等于原函数；不让调用者提供所求结果 | 新验证的主库替换为 0；不作普遍不可能断言 |
| 改用有效表示 | 用有限律、可判定事件、有效数值编码等运算，证明其解释等于原数学对象或指定观测 | 多类可行；具体假设与证明覆盖见下文及清单 |
| 数值计算 | 对有效编码的输入及任意正有理误差，终止并输出满足误差界的有理数 | 有限期望、吸收链、终端期望逼近已有特例；原任意路径效用有明确障碍 |

Lean 的 `noncomputable` 管理代码生成；证明中的经典选择不自动成为运行时依赖。
依赖图或第一条编译错误都不能代替对数据字段的检查。
参见 [Lean 定义修饰符说明](https://lean-lang.org/doc/reference/latest/Definitions/Modifiers/)。

还应区分“能返回一个 Lean `ℝ` 对象”和“能计算到指定精度”。当前 Mathlib 的
`Real.mk` 接收有理 Cauchy 序列，其 Cauchy 性是 `Prop` 中的存在量词，
没有随对象提供可执行的收敛速度。因此，本报告关于数值求值器的否定结论，
不能直接升级为“不存在任何返回 `ℝ` 的 Lean 可编译项”。
源码依据为 [Real.mk](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Data/Real/Basic.lean)
和 [IsCauSeq](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Algebra/Order/CauSeq/Basic.lean)。

## 2. 58 项按主要处理路线分组

分组互斥，用于安排实现工作；不表示每项只有一种依赖，也不表示全部已有通用实现。

| 组 | 数量 | 可行计算及原接口边界 |
|---|---:|---|
| F：已有有限数据或确定性操作 | 9 | 复用原有限原子、纯策略或历史追加；测度嵌入仍保留。S112、S113 另需可执行终止判断 |
| K：一步核与策略装配 | 12 | 有效动作律和转移律上用 `bind`、`map`；一般可测核没有自动提供这些有限数据 |
| M：给定测度的推前 | 3 | 有效事件可求逆像；可测嵌入已有同测度结果的正面对照，但三项原映射不保证是嵌入 |
| P：有限时间边缘与前缀 | 9 | 有效一步律上有限迭代；不需先数值构造无限轨迹，仍须保持历史、动作和时钟 |
| T：完整路径律 | 18 | 可提供一致的有限柱事件计算；有界终止时有有限支持的完整路径表示；一般完整 `Measure` 未被替换 |
| I：期望效用 | 5 | 有限有理求和、有限吸收链精确解，或附条件的正容差逼近；一般积分未被替换 |
| Q：条件分布版本 | 1 | 已有续局版本的几乎处处等式，正质量前缀处逐点相等；零质量前缀上的原选定版本不能擅自改变 |
| E：任意原始路径上的最终效用 | 1 | 全域终止的有限查询数值求值器不可行；限制到可判定终止且必达的合法吸收路径才可搜索 |
| 合计 | **58** | 原签名的普遍不可实现性没有被这张分类表证明 |

## 3. 有限数据与一步执行：优先提取，但不得混淆接口

F 组的 9 项是 S083、S084、S087、S103、S112、S113、S127、S128、S129。
`ofFiniteLaw` 已收到有限原子；`ofPure` 已收到唯一原子；混合策略已能构造
`pureProfileLaw`；离散历史模型的追加本身也可计算。主要剩余工作是有限律到
`Measure`/`Kernel` 的解释，而非求出未知分布。输入函数本身仍须具有可执行实现。

S113 是需另行处理的例外：原函数对任意状态判断 `IsEmpty (A.Action state)`，
终点返回零动作测度，非终点才调用有限策略。原类型没有给出该命题的运行时决定程序。
S112 继承这一问题。应提供终止决定或带终点分支的有限律接口；
不能在空动作类型上构造规范化有限分布。状态演化的终点吸收则是另一个分支。

K 组的算法形状是先取动作、再转移，并用 `map` 保留动作记录或实现映射。
原核可以是非原子的；换成有限律是增加有效表示条件。
主库 `Execution/Discrete/HistoryKernel.lean` 现已实现任意有限律的通用状态／事件
历史执行；`Simulation/Kernel/FiniteExecution.lean` 在局部可测实现条件下证明了一步
以及从任意初始前缀出发的任意有限步 `partialTraj` 等式。它没有把任意历史函数
自动认作可测，也没有改变一般非原子核的输入契约。
主库 `Execution/Discrete/FiniteObservation.lean` 又将同一执行结果投影为精确坐标律、
尾部前缀律和任意绝对时界的前缀律，因而不需要先构造无限路径测度。
事件策略始终在包含历史动作的前缀上执行，状态坐标只在执行完成后投影。

## 4. 测度推前：有正面例子，不能以返回类型判死刑

新证据 [LibraryFeasibility.lean](../research/efg-computability/LibraryFeasibility.lean)
实现了可编译的 `mapEmbedding μ f hf`，并证明
`mapEmbedding_eq : mapEmbedding μ f hf = μ.map f`。
这里 `hf : MeasurableEmbedding f`，测度 `μ` 是原始输入。
函数直接设置外测度的数据字段 `s ↦ μ (f ⁻¹' s)`，将相关证明放在擦除的字段中。
编译检查确认它不被标记为不可计算。这反驳了“返回 `Measure` 就必然不能编译”。

但 S082 的坐标投影、S085 的任意可测求值器、S086 的路径执行器都不保证可测嵌入。
一般推前的外测度有 `trim`；只在可测集上知道逆像公式，不能直接将其用于所有集合。
因此这个正面对照未消除三项原声明，也没有构造其输入测度。
参见 Mathlib 的 [map 与可测嵌入公式](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/Map.lean)。

类似地，有限 Dirac 采样极简单，但任意 `Set α` 的成员资格是 `Prop`。
有限载体并不自动给任意事件提供可执行判定。第一条错误若是
`ENNReal.instCommSemiring`，也不能据此认定该字典是任何等价实现都不可绕过的障碍。

## 5. 有限边缘与完整路径：无限时域不等于无法计算概率

P 组可以绕过“先造无限轨迹再投影”的计算顺序。源码已有
`prefixMeasure_eq_partialTraj` 等有限迭代等式；在有效有限动作与转移律、
终止判断和有限事件描述下，用有限次 `bind` 即可计算指定前缀或坐标概率。
`unfinishedMass` 还需要可判定的非终止事件；时间有限不自动补足这项输入。

T 组可采用 `horizon ↦ finitePrefixLaw horizon` 的有效表示。
每个有限柱事件都可能精确可算，即使不存在统一终止界、甚至路径从不终止。
需证明前缀一致性及与原路径测度的柱事件等式，不能仅交付一组无一致性证明的边缘。
主库 [RationalIntervalUnion.lean](../../EconCSLib/Math/Probability/RationalIntervalUnion.lean)
给出有限有理区间并集的纯容斥算法；其独立
[Volume 语义叶](../../EconCSLib/Math/Probability/RationalIntervalUnion/Volume.lean)
证明该值等于原单位区间非原子体积并位于 `[0,1]`。这只计算有效描述的事件，
不把任意实数集合成员资格或一般非原子测度冒充为有限可计算对象。
A19 的 `UniformUnitInterval` backend 现在把这项算法包装成真正的非原子
`EffectiveLaw` 和常值 `EffectiveKernel`；`UniformSemantics` 证明其 enclosure 表示
volume。通用 `EffectiveKernel` 以 simple-observable pullback 表示，使 law bind 与
kernel composition 可执行。事件语言仍必须对调用者需要的 preimage 和 pullback
封闭；一般连续 backend 要另给自身的数值积分与误差传播。
可计算测度采用有效表示这一背景参见
[Hoyrup–Rojas](https://arxiv.org/abs/0709.0907)；这里的具体有限迭代路线依据仓库源码。

主库 `Execution/FiniteCompletePath.lean` 已处理“所有正质量原子在给定界内终止”的特例，
由有限终点按需计算完整吸收路径坐标，并证明所有坐标边缘与原有限执行一致；
示例中的 `exists_pathLaw` 仍只是该有限律的分析解释存在定理。
它不能覆盖原声明允许的所有非原子、无界轨迹。
S081 等包装器依赖完整路径律，提供一个已算好的完整律再包装不构成原任务的算法。

续局和重启还须保留三个区别：绝对时间、完整入局历史、动作的发生记录。
S134 只清理尾路径第零坐标的入射动作标记，并不重新启动策略时钟。
S133 的新时钟重启也不自动等于原绝对时间续局。
`FiniteObservation.lean` 已把这两条有限路线分开：`absolutePrefixLawFrom`
保留旧前缀和绝对时钟，`freshPrefixLaw` 从最新状态以时间零执行，
`splicedFreshAbsolutePrefixLawFrom` 再丢弃重复的 fresh 零坐标并拼回旧前缀。
请求时界不超过旧前缀时，两条路线都只返回精确截断的纯律。
`Simulation/Restart/FiniteExecution.lean` 已进一步对每个时界证明这三类
`FiniteLaw` 的 Dirac 解释分别等于原 `absoluteFinitePrefixMeasureFromPrefix`、
`freshRestartFinitePrefixMeasure` 和 `splicedFreshFinitePrefixMeasure`；这项桥接
直接使用原 restart 定义，而不是另设一套较弱语义。

## 6. 条件续局：已有可用版本，但全域逐点相等是额外要求

S088 调用一般 `condDistrib`。对一般输入，可计算联合分布并不保证条件分布可计算，
参见 [Ackerman–Freer–Roy](https://arxiv.org/abs/1005.3014)。
**这不是对本声明的不可能性证明**：本声明额外提供了生成过程的策略和转移结构。

在 [Conditioning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean)
中，`conditionalTailKernel_ae_eq_continuationTailKernel` 已证明直接续局版本与
原条件核几乎处处相同；`conditionalTailKernel_eq_continuationTailKernel_of_prefix_ne_zero`
进一步在可测、正质量的前缀原子处给出逐点等式。
因此有效模型可计算该续局版本的有限未来观测，无须从联合律重新做一般解体。
主库 `Execution/Discrete/ConditionalContinuation.lean` 进一步提供有限原子先验上的
精确 Bayes 续局：Arena 完整历史以及 KernelArena 状态／动作事件前缀都保留原历史
与绝对时钟，零质量观测返回 `none`。
主库 [FiniteConditioning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/FiniteConditioning.lean)
又证明：成功计算的有限 posterior 续局的 Dirac 测度解释，等于把
posterior 的可测前缀重索引后与原 `partialTraj` 做 measure bind，也等于
`absolutePathMeasureFromPrefix` 的指定有限前缀边缘混合。该桥接不需要
在零质量前缀上选择正则条件分布。

零质量前缀上不承诺与 Mathlib 选定版本相等。把这处返回值改成任意续局，
对几乎处处语义可能足够，对原核作为全域函数的逐点等价则不够。
S089 本身仍构造完整路径核，因此也需要 T 组的表示和证明。

## 7. 期望：可积性、误差界、可执行搜索各有作用

I 组包括普通路径期望、其有界包装，以及起点/续局的最终终端期望。
有界性或可积性只提供数学保证；原签名没有自动给出任意核和任意路径收益的有效积分算法。
可采用以下已有但有明确范围的结果：

| 现有文件 | 已证明的计算语义 | 不能省略的范围 |
|---|---|---|
| [Execution/FinitePayoff.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/FinitePayoff.lean) | Arena 完整历史及 KernelArena 状态／事件前缀上的精确有理期望与停止收益 | 有限执行、可判定终止和有理收益 |
| [Execution/Truncation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Truncation.lean) | 精确停止收益中心、未完成质量半径、预算搜索及显式存在证明保护的最小时界搜索 | 有理收益界；分析层仍须证明误差时界存在，零容差没有一般保证 |
| [Simulation/Equilibrium/FinitePayoff.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/FinitePayoff.lean) | 上述精确有理结果等于有限 Dirac 积分、带有限边缘一致证书的完整路径坐标积分，以及状态／动作事件 `partialTraj` 积分；分析未完成质量等于可执行 `unfinishedMass`，且计算半径给出积分误差界 | 仍是有限时界和有理观测；所给完整路径律必须显式证明与可执行边缘一致；误差定理保留目标的可积性、有界性和终止一致前提 |
| [FiniteLawIntegral](../../EconCSLib/Examples/ExtensiveGame/FiniteLawIntegral.lean) | `integral_eq_expectRat`：有限有理加权和等于积分 | 给定有限律与有理收益 |
| [FiniteExecutionIntegral](../../EconCSLib/Examples/ExtensiveGame/FiniteExecutionIntegral.lean) | `historyLaw_eq_coordinate`、`integral_stoppedUtility`：保留历史的有限执行与停止收益 | 相应离散有效模型和有限时界 |
| [FiniteMarkovChain/Semantics.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/Semantics.lean) | `autoCheck_iff_absorbsAll`、`autoSolve_correct`：自动全域吸收检查充要；成功后精确解等于首达收益／时间积分 | 固定有限有理 Markov 链；原状态编码必须保留所需历史，不能把任意 EFG 端点自动商成 Markov 状态 |
| [Effective/Semantics.lean](../../EconCSLib/Math/Probability/Effective/Semantics.lean)、[EffectivePathUtility.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/EffectivePathUtility.lean) | 有效 law 对有限有理 simple observable 的 expectation oracle 包含真实积分；observable `Denotes` 玩家 utility 时表示原 S101 `expectedUtility` | 调用者选择事件语言并提供 law representation 与 `Denotes` 证书；任意 `Integrable` 函数不会自动获得有限表示或有效误差模数 |
| [FiniteTruncation](../../EconCSLib/Examples/ExtensiveGame/FiniteTruncation.lean) | `approximate_correct`：正容差的有理估计对应原最终效用积分 | 有效有限策略、终止判定、有理收益及界、相应可数历史模型、几乎必达证明 |

最后一项从几乎必达推出未完成质量趋零，再搜索满足可判定误差界的时界。
**不需要调用者另外交付收敛速度或所求积分值**；存在性证明用于保证搜索终止。
但零容差、一般无界路径收益、任意分析核不能自动使用这个算法。
一般有限随机转移与绝对前缀的有限收益积分等式已进入主库；
从几乎必达推导截断搜索的存在证明及与一般 eventual utility 积分的误差界仍属分析层工作。

## 8. 最终路径效用：明确的数值计算障碍

S099 在每条原始无限路径上全定义：若最终永久停在某个终端历史则取该处收益，
否则返回零。它检查的是“存在一个时刻，此后所有时刻都保持同一终端历史”，
而不是“是否曾经到达过终点”。源码接受的原始路径不限于合法、吸收或必达路径。

新证据在实际 repeat-or-stop EFG 中证明：对每个有限时界 H，都存在两条路径，
前 H 项完全相同，但原 `eventualUtility` 分别为 0 和 1。
一条永远停在非终点，另一条在 H 时刻转到收益为 1 的终点并永久停留。
证明名为 `no_finite_prefix_determines_value` 与 `repeatOrStop_prefixWitness`。
这些路径用于测试原函数的全域契约；无需额外宣称它们满足轨迹合法性。

如果一个数值求值器在永不终止路径上也必须终止，它只能查询有限多个坐标。
取 H 大于所有已查询坐标，另一条路径给出完全相同的查询答案，但正确值相差 1。
同一个输出无法同时满足两者小于 1/3 的误差要求。
这是对**有限查询、全域终止、保证数值误差的算法**的否定；
Lean 文件形式化了路径及数值见证，有限查询机器的论证写在这里，没有伪称已形式化。

若限定合法吸收路径、给可执行终止判定和到达证明，可搜索第一次命中并取收益；
给定时界则可用已有 `stoppedUtility`。这改变了原输入域或输出契约。
几乎必达只支持几乎处处的行为和积分结果，不使每条原始路径上的搜索都终止。
本节也不证明任何返回弱 Cauchy 表示 `ℝ` 的 Lean 项都不可能存在，见第 1 节。

## 9. 实现次序与证据边界

F/K/P 组的第一批主库基础已落在 `FiniteLaw`、`HistoryKernel` 和
`Simulation/Kernel/FiniteExecution`；有限收益、正质量条件续局、有界终止完整路径
及纯截断搜索也已有主库落点，有限 restart 的三类原分析测度也已有全时界等式。
下一阶段是把剩余分析层的存在性、一般路径积分与条件分布定理接到相应有效对象，
并为实际连续模型增加符合 A19 闭包契约的 backend，继续逐项验证表示差异。
一般分析定义继续作为精确数学语义；只有真正完成同签名等价实现时才删其修饰符。
有效子域的算法不会使较一般的分析定义过时；消费者迁移遵循
[语义兼容层](efg-semantic-compatibility.md)的所有权与证据规则。
文件落点继续参照[整个 EFG 文件规划](efg-file-plan.md)。

本轮证据使用 Lean 4.30.0 和仓库锁定的 Mathlib 提交
`c5ea00351c28e24afc9f0f84379aa41082b1188f`。
58 项修饰符探针与原源码范围一一对应。
独立 Lean 文件可用以下命令复核：

```bash
lake env lean docs/research/efg-computability/LibraryFeasibility.lean
```

它检查推前构造可编译，并列出三个关键定理的公理依赖：仅
`propext`、`Classical.choice`、`Quot.sound`，无占位证明或运行时代替证明的公理。
这些有限的正反证据支持上面的分层结论，不是 58 个通用实现，也不是 58 个不可实现性定理。

验证记录：上述 Lean 证据、58 项覆盖/源码摘要、文档治理、占位检查和差异空白检查通过。
另对现有 Lean 编译环境查询，得到主库 58、示例 79、合计 137 项，分类证据核对通过。
标准 `check_efg_computability.py` 已在重建主库与示例聚合后通过；
它同时核对 Lake 依赖新鲜度、137 项分类证据和零新增基线。
