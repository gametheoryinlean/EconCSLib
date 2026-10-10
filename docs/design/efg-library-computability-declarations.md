# EFG 主库 58 项可实现性逐项清单

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

复核日期：2026-09-04。此表与[严格分析](efg-library-computability.md)配套，
覆盖 S081–S138，每项恰好一次。原完整签名及源码摘要见
[分类记录](../../scripts/efg_computability_classification.json)。

**共同结论：58 项只删修饰符都不能编译，本轮均未验证原签名的等价可编译替换。**
表中“路线”明确写出有效表示、额外输入及语义限制；不是已完成通用实现的标记。
编译阻碍列只记录当前函数体的首条诊断，不将其解释为任何改写都无法绕过的依赖。
有限算法、一般分析定义及对应定理的生命周期术语遵循
[语义兼容层规则](efg-semantic-compatibility.md)：分析定义不因有限有效特例可执行而
称为 legacy。
除有限律路线外，A19 已实现选定事件码／有限有理 simple-observable 子域的有效
law、pushforward、kernel bind/composition 与非原子单位区间 backend。它是带明确
表示证书的有效子域，不是任意 `Set`、`Measure` 或可积函数的同签名替换。

| 组 | 主要路线 | 数量 |
|---|---|---:|
| F | 已有有限数据或确定性操作 | 9 |
| K | 一步核与策略装配 | 12 |
| M | 给定测度的推前 | 3 |
| P | 有限边缘与前缀 | 9 |
| T | 完整路径律 | 18 |
| I | 期望效用 | 5 |
| Q | 条件分布版本 | 1 |
| E | 原始无限路径的最终效用 | 1 |

源码链接定位原声明，组别只是主要路线；包装器可能同时继承多个分析依赖。
既有有限计算与积分证明的范围统一见[分析第 7 节](efg-library-computability.md#7-期望可积性误差界可执行搜索各有作用)。
新推前正面对照和最终效用的路径见证见
[LibraryFeasibility.lean](../research/efg-computability/LibraryFeasibility.lean)。

## [Observed/Controlled/Law/Analytic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law/Analytic.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S081 [`ObservedGame.MeasurableKernelPresentation.kernelBehavioralCompletePathLawSemantics`](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law/Analytic.lean#L40) | T | `KernelBehavioralProfile.statePathMeasure` | 包装策略装配后的状态路径律及坐标边缘；合法性证书在证明字段。 **路线：**先实现有效 profile 的路径表示和一致边缘，再接此包装；交付预先算好的路径律不是原构造的实现。 |

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|

## [Simulation/Continuation/Conditioning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S088 [`EventHistoryActionPolicy.conditionalTailKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean#L88) | Q | `condDistrib` | 原结果是 condDistrib 选定的全域条件核；生成策略同时可用。 **路线：**源码已证直接续局版本几乎处处相等，正质量可测前缀原子处逐点相等；有效一步律可算未来有限观测，但不擅改零质量前缀上的版本。 |
| S089 [`EventHistoryActionPolicy.continuationTailKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean#L43) | T | `Kernel.map` | 直接由 traj 和尾路径映射构造续局核，没有调用 condDistrib。 **路线：**有效一步律上保留绝对时间和全部给定前缀，计算有限未来柱事件；完整 Measure 核仍需路径解释。 |

## [Simulation/Continuation/Observed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S090 [`ObservedGame.MeasurableHistoryModel.BoundedPathUtility.continuationExpectedUtility`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean#L398) | I | `integral` | 对原完整续局路径积分任意有界路径效用；有界性不是有效收益表示。 **路线：**有限完整路径及有效有理收益可精确求和；更一般逼近需有效收益与误差控制。终端截断算法不能直接处理任意路径效用。 |
| S091 [`ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension.continuationExpectedEventualUtility`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean#L853) | I | `integral` | 续局中的最终收益积分，带原续局几乎必达证明。 **路线：**有效有限律、有理终端收益及界下可搜索截断误差；需把已有离散证明推广到此绝对前缀续局，不能重置时钟或要求调用者给积分答案。 |
| S092 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.continuationEventPathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean#L236) | T | `MeasurableKernelArena.EventHistoryActionPolicy.tailEventPathMeasureFromPrefix` | compiledPolicy 在给定完整历史根的绝对前缀续局事件律。 **已实现子域：**显式 effective profile 在 discrete complete-history model 上保留完整 canonical prefix 和绝对时钟，有限迭代后 tail reindex；`effective_measure_tailPrefixLawFrom_eq_continuationEventPathMeasure_map_frestrictLe` 证明每个有限边缘等于原完整律的投影。 |
| S093 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.continuationStatePathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean#L247) | T | `MeasurableKernelArena.EventHistoryActionPolicy.tailStatePathMeasureFromPrefix` | 由相同绝对前缀续局取得完整状态路径律。 **已实现子域：**先保留事件历史执行，再 map 状态投影；`effective_measure_tailPrefixLawFrom_map_states_eq_continuationStatePathMeasure_map_frestrictLe` 给出每个有限 state-prefix 边缘，因此没有删除动作历史对后续策略的影响。 |
| S094 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.freshRestartStatePathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean#L355) | T | `statePathMeasure` | 从给定根按时间零调用 statePathMeasure，是新时钟重启。 **已实现子域：**`effective_measure_finitePrefixLawFrom_map_states_eq_freshRestartStatePathMeasure_map_frestrictLe` 从 time zero 生成并逐 horizon 对接原测度；它不以绝对时钟续局替换 fresh restart。 |

## [Simulation/Continuation/Path.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Path.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S095 [`EventHistoryActionPolicy.absolutePathMeasureFromPrefix`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Path.lean#L45) | T | `Kernel.traj` | Kernel.traj 从 start 和整个 initialPrefix 生成绝对坐标路径。 **路线：**有效一步律可逐步延伸给定前缀；结果须同时保留 start 前的固定部分和此后的绝对时间策略。 |
| S096 [`EventHistoryActionPolicy.tailEventPathMeasureFromPrefix`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Path.lean#L101) | T | `Measure.map` | 对 S095 作尾路径推前，删除早期坐标但没有重启策略。 **路线：**有限未来观测用绝对时钟延伸后截取；有界终止可给有限支持路径特例，普通完整律不因此编译。 |
| S097 [`EventHistoryActionPolicy.tailStatePathMeasureFromPrefix`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Path.lean#L240) | T | `Measure.map` | 续局事件律再作状态投影。 **路线：**在 S096 的有效表示上 map 状态，保留生成时的事件历史依赖；需状态投影对应等式。 |

## [Simulation/Equilibrium/Outcome.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S098 [`ObservedGame.MeasurableHistoryModel.BoundedPathUtility.expectedUtility`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean#L200) | I | `PathUtility.expectedUtility` | 有界路径效用包装 S101，界用于可积性证明。 **路线：**沿 S101 的有效积分路线；有限路径收益若是有理有效数据可精确求和，有界证书本身不补充计算算法。 |
| S099 [`ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension.eventualUtility`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean#L823) | E | `Classical.propDecidable` | 对任意原始路径判断最终永久停在终端，否则返回零；不是第一次命中。 **路线：**新证明给出每个有限前缀下 0/1 不可区分见证，排除全域终止的有限查询数值算法。限定合法吸收且必达、可判定终止后才可搜索；未证明所有 Lean 实数项均不可能。 |
| S100 [`ObservedGame.MeasurableHistoryModel.BoundedTerminalPayoffExtension.expectedEventualUtility`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean#L979) | I | `integral` | 积分 S099，原签名有几乎必达证明；积分只需几乎处处语义。 **路线：**已有离散 FiniteTruncation 用有效有限执行、有理收益及界、正容差搜索估计。有限有理吸收链还可精确解；非原子核不能直接套用。 |
| S101 [`ObservedGame.MeasurableHistoryModel.PathUtility.expectedUtility`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean#L99) | I | `integral` | 任意可测路径收益的 Bochner 积分，IntegrableAt 作为证明输入。 **已建有效路线：**表示原 state-path Measure 的 `EffectiveLaw` 可计算有限有理 `SimpleObservable` expectation oracle；若调用者证明该 observable `Denotes` 玩家 utility，`effective_expectedUtility_represents` 证明 oracle 表示原积分。任意可积函数不会自动产生有限表示或误差模数。 |
| S102 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.unfinishedMass`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean#L696) | P | `statePathMeasure` | 在有限时间坐标上取非终止事件质量，原实现经过完整状态路径律。 **路线：**有效有限前缀可直接累加未终止原子；还需可执行终止判定。现有离散 noneMass 与 measure_unfinished 给出特例桥接。 |

## [Simulation/Kernel/Arena.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Arena.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S103 [`KernelArena.toMeasurable`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Arena.lean#L175) | F | `ENNReal.instCommSemiring` | KernelArena 已携带 next 的有限律；函数逐点把它嵌入测度。 **路线：**直接复用 next 进行有限计算，保留原解析嵌入；不必额外枚举整个状态空间，但原核返回值未得到可编译替换。 |

## [Simulation/Kernel/EventPath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S104 [`EventHistoryActionPolicy.actionStepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L336) | K | `Kernel.comp` | 事件前缀动作核与 recordedTransition 组合，包含实际选中动作。 **已建有效路线：**`HistoryKernel` 以有限动作律 bind 有限转移律并 map 成带动作的后继事件；`FiniteExecution` 已证明局部可测实现下的一步核等式。 |
| S105 [`EventHistoryActionPolicy.coordinateMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L478) | P | `Measure.map` | 完整事件路径律在 time 的坐标边缘。 **已建有效路线：**`FiniteObservation.EventHistoryPolicy.eventCoordinateLawFrom` 计算完整有限事件前缀后投影该坐标；`FiniteExecution.measure_eventCoordinateLawFrom_eq_partialTraj_map` 直接证明其 `partialTraj` 分析解释，仍要求有效策略、终止判断和局部可测实现。 |
| S106 [`EventHistoryActionPolicy.pathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L436) | T | `Kernel.traj` | 事件路径的 Ionescu–Tulcea 轨迹构造，从初始事件开始。 **路线：**有效一步事件律可计算一致有限前缀；有界终止时可有限支持表示全路径，任意无限轨迹不作该承诺。 |
| S107 [`EventHistoryActionPolicy.pathStepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L363) | K | `Classical.propDecidable` | 原始事件前缀的 terminal 分支选择吸收事件，否则调用 S104。 **路线：**增加可执行终止判断，终点 pure 原吸收事件，非终点有限 bind；保持原吸收时的事件记录约定。 |
| S108 [`EventHistoryActionPolicy.prefixMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L469) | P | `Measure.map` | 从完整事件路径中提取有限前缀。 **已建有效路线：**`HistoryKernel.prefixLawFrom` 用有限 bind 保留每个事件，`FiniteExecution.measure_prefixLawFrom_eq_partialTraj` 证明其任意步分析解释。 |
| S109 [`EventHistoryActionPolicy.stateCoordinateMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L509) | P | `Measure.map` | 事件坐标再投影成状态坐标。 **已建有效路线：**`FiniteObservation.EventHistoryPolicy.stateCoordinateLawFrom` 在完整事件前缀执行后 map 状态；`FiniteExecution.measure_stateCoordinateLawFrom_eq_partialTraj_map` 证明其 Dirac 解释等于分析事件执行的状态坐标边缘。 |
| S110 [`EventHistoryActionPolicy.statePathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L487) | T | `Measure.map` | 完整事件路径经逐坐标状态投影。 **路线：**在 S106 的有效柱事件表示上处理状态查询；若声称原 Measure 相等，必须给出完整律的投影对应。 |
| S111 [`recordedTransition`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean#L202) | K | `Kernel.map` | 将转移输出与实际输入动作捆绑，得到 recordedTransition。 **路线：**有效有限转移律上 map 成 PathEvent；原转移允许非原子输入，有限表示不是从 Kernel 类型自动取得的。 |

## [Simulation/Kernel/Execution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S112 [`KernelArena.Policy.toMeasurable`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean#L417) | F | `toMeasurableKernel` | 包装 S113 并证明合法性与终点零质量，证明不是运行时负担。 **路线：**计算侧返回带终点分支的有限动作律；原 policy 尚缺全状态终止判定，且原 ActionPolicy 仍携带分析核。 |
| S113 [`KernelArena.Policy.toMeasurableKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean#L331) | F | `Classical.propDecidable` | 有限 policy 仅在非终点供给动作律；这里经典判断动作类型是否为空。 **路线：**补可执行 IsEmpty 判定或使用带终点信息的接口；终点零律、非终点原有限律。有限数据已在输入中，但原域分支并不可自动判定。 |
| S114 [`ActionPolicy.actionStepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean#L120) | K | `Kernel.comp` | 动作核与 arena 转移核的组合。 **路线：**有效有限动作/转移用 bind，保留 dependent action 的所属状态；一般任意核组合涉及积分，未有原签名编译替换。 |
| S115 [`ActionPolicy.stepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean#L128) | K | `Classical.propDecidable` | 在 terminalSet 上取恒等吸收核，否则 S114。 **路线：**需要可执行终止判断及有效非终止一步律；终点返回 pure 当前状态。MeasurableSet 证书不提供运行时判断。 |

## [Simulation/Kernel/HistoryPath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S116 [`HistoryActionPolicy.actionStepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean#L128) | K | `Kernel.comp` | 完整状态前缀动作核再组合转移核。 **路线：**用 finite bind，策略输入保留整个状态前缀及 time；现有具体示例不能代表任意历史依赖核已有实现。 |
| S117 [`HistoryActionPolicy.coordinateMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean#L230) | P | `Measure.map` | 状态历史路径在 time 的边缘。 **已建有效路线：**`FiniteObservation.StateHistoryPolicy.coordinateLawFrom` 在保留完整历史和绝对时钟的有限迭代之后投影指定坐标；`FiniteExecution.measure_coordinateLawFrom_eq_partialTraj_map` 给出直接的分析边缘等式。 |
| S118 [`HistoryActionPolicy.pathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean#L205) | T | `Kernel.traj` | 状态历史依赖的完整轨迹构造。 **路线：**有效一步律计算一致有限状态前缀；未承诺用有限对象替代任意完整 Measure。 |
| S119 [`HistoryActionPolicy.pathStepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean#L136) | K | `Classical.propDecidable` | 对完整状态前缀判断最新状态是否终止，再选择吸收或 S116。 **路线：**可执行终止判定加 finite bind，终点保持最新状态；可测终止集合不等于可决定谓词。 |
| S120 [`HistoryActionPolicy.prefixMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean#L222) | P | `Measure.map` | 状态历史路径的有限前缀边缘。 **已建有效路线：**`HistoryKernel.prefixLawFrom` 计算完整状态前缀，`FiniteExecution.measure_prefixLawFrom_eq_partialTraj` 对任意初始前缀和步数证明分析等式；策略仍可依赖完整前缀。 |

## [Simulation/Kernel/RealizedInformation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/RealizedInformation.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S121 [`EventInformation.RealizedActionPolicy.realizedKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/RealizedInformation.lean#L264) | K | `Kernel.snd` | 先抽象动作采样，再依赖具体前缀的实现核，最后忘掉抽象动作。 **路线：**两阶段都需有效律，用 bind 保留原前缀参与 realization；实现核本身也可随机，不得假定只是确定映射。 |
| S122 [`EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/RealizedInformation.lean#L301) | K | `realizedKernel` | 把 S121 作为事件历史动作核，并装入证明字段。 **路线：**先完成实现动作的有限核与对应，再包装；仅把原 realizedKernel 换成外部供给的结果不构成计算实现。 |

## [Simulation/Kernel/StatePath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/StatePath.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S123 [`ActionPolicy.pathStepKernel`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/StatePath.lean#L78) | K | `stepKernel` | 将状态依赖 S115 沿最新状态投影拉回到前缀。 **路线：**最新状态投影已可计算；实际障碍继承 S115 的终止分支和有效一步核，无需新增独立轨迹算法。 |

## [Simulation/Presentation/Chance/Measurable.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Measurable.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S124 [`ObservedChanceGame.MeasurablePresentation.compiledPolicy`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Measurable.lean#L178) | K | `MeasurableKernelArena.EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy` | 把 chance presentation 的 realized policy 包成事件历史策略。 **路线：**利用原行为有限律、机会有限律与角色/终止决定，证明计算动作律等于原 realization；不能假定任意 presentation 已给可执行核。 |
| S125 [`ObservedChanceGame.MeasurablePresentation.eventPathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Measurable.lean#L299) | T | `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | S124 生成完整事件路径律，包含玩家与机会动作。 **路线：**先有对应的有效装配策略，再计算一致有限事件前缀；一般完整测度仍由分析层提供语义。 |
| S126 [`ObservedChanceGame.MeasurablePresentation.statePathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Measurable.lean#L309) | T | `MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure` | chance presentation 的事件路径遗忘动作得到状态路径。 **路线：**从 S125 的有效事件执行投影；机会分支、玩家信息和原历史在生成阶段仍要保留。 |

## [Simulation/Presentation/Chance/MeasurableHistory.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/MeasurableHistory.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S127 [`ObservedChanceGame.MeasurableHistoryModel.discrete`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/MeasurableHistory.lean#L263) | F | `ObservedGame.MeasurableHistoryModel.discrete` | chance 版本 discrete 是 S128 的兼容别名。 **路线：**复用 observed 历史追加的有限计算；没有独立概率求解，继承 S128 的测度嵌入边界。 |
| S128 [`ObservedGame.MeasurableHistoryModel.discrete`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/MeasurableHistory.lean#L167) | F | `KernelArena.toMeasurable` | top 可测历史模型，转移要求精确等于 Dirac appendHistory。 **路线：**appendHistory 与 historyKernelArena 的单原子有限转移已可计算；可测空间证书不要求历史有限，原模型仍含 Dirac 核。 |

## [Simulation/Presentation/Chance/Realized.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Realized.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S129 [`ObservedChanceGame.AnalyticHistoryArena`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Realized.lean#L77) | F | `KernelArena.toMeasurable` | chance 完整历史 arena 的 toMeasurable 别名。 **路线：**直接使用原 historyKernelArena 的有限操作；完整分析 arena 的返回值继承 S103 的嵌入边界。 |

## [Simulation/Presentation/Kernel/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/Core.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S130 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.compiledPolicy`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/Core.lean#L150) | K | `MeasurableKernelArena.EventInformation.RealizedActionPolicy.toEventHistoryActionPolicy` | kernel-valued behavioral profile 通过 S122 装配事件历史策略。 **路线：**要求抽象策略及 realization 有有效表示，再沿 S121/S122 证明对应；原核值 profile 不自动具有有限支持。 |
| S131 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.eventPathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/Core.lean#L360) | T | `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | kernel behavioral profile 通过 S106 构造完整事件路径律。 **路线：**有效装配与终止决定后计算前缀；非原子 profile、无界路径仍保留一般分析语义。 |
| S132 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.statePathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/Core.lean#L369) | T | `MeasurableKernelArena.EventHistoryActionPolicy.statePathMeasure` | kernel behavioral profile 的完整状态路径律。 **路线：**从 S131 的有效事件表示投影状态；不能按返回类型把历史信息约束简化为 Markov 性。 |

## [Simulation/Restart/Observed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Observed.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S133 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.freshRestartEventPathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Observed.lean#L35) | T | `MeasurableKernelArena.EventHistoryActionPolicy.pathMeasure` | 从 root 在时间零重启生成事件路径。 **路线：**有效策略从新时钟计算柱事件；与绝对时间续局是否相同取决于额外重启兼容定理。 |
| S134 [`ObservedGame.MeasurableKernelPresentation.KernelBehavioralProfile.normalizedContinuationEventPathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Observed.lean#L44) | T | `Measure.map` | 绝对前缀续局的第零尾事件被 freshenInitialEvent 规范化。 **路线：**对有效续局前缀 map 该已有确定性变换；它只改初始事件标记，不能顺便重置时间或策略信息。 |

## [Simulation/Restart/Trajectory.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean)

| ID / 原声明 | 组 | 当前编译阻碍 | 逐项判断与可行路线 |
|---|---|---|---|
| S135 [`EventHistoryActionPolicy.absoluteFinitePrefixMeasureFromPrefix`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean#L173) | P | `Measure.map` | 绝对续局完整律截取到 horizon，horizon 可早于 start。 **已建有效路线：**`FiniteObservation.EventHistoryPolicy.absolutePrefixLawFrom` 在 `horizon ≤ start` 时返回旧前缀的纯截断律，否则以原绝对时钟执行 `horizon - start` 步；`measure_absolutePrefixLawFrom_eq_absoluteFinitePrefixMeasureFromPrefix` 已对任意 horizon 证明其 Dirac 解释等于原声明。 |
| S136 [`EventHistoryActionPolicy.freshRestartFinitePrefixMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean#L198) | P | `Kernel.partialTraj` | 从最新状态在时间零用 partialTraj 跑到 offset。 **已建有效路线：**`FiniteObservation.EventHistoryPolicy.freshPrefixLaw` 只从旧前缀取最新状态，用 `EventPrefix.initial` 在时间零直接递归执行精确有限律；`measure_freshPrefixLaw_eq_freshRestartFinitePrefixMeasure` 证明其 Dirac 解释等于原声明。 |
| S137 [`EventHistoryActionPolicy.splicedFreshAbsolutePathMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean#L59) | T | `Measure.map` | 把原固定前缀与从最新状态新启动的完整路径拼接。 **路线：**用已有拼接函数作用于有效路径表示，证明对应推前；它是新时钟拼接，不自动等于 S095。 |
| S138 [`EventHistoryActionPolicy.splicedFreshFinitePrefixMeasure`](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean#L185) | P | `Measure.map` | S137 的有限绝对前缀边缘。 **已建有效路线：**`FiniteObservation.EventHistoryPolicy.splicedFreshAbsolutePrefixLawFrom` 在旧前缀内纯截断，在其后以时间零生成 fresh continuation，删去重复的零坐标后拼接；`measure_splicedFreshAbsolutePrefixLawFrom_eq_splicedFreshFinitePrefixMeasure` 已对任意 horizon 证明原语义等式。 |
