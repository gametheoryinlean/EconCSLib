# EFG 有限与无限问题的算法机会审计

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

**复核日期：**2026-09-04

**范围：**EFG 主库 S081--S138 共 58 个 `noncomputable` 声明；不含 `Examples/`

**地位：**对
[`efg-library-computability.md`](efg-library-computability.md)和
[`efg-library-computability-declarations.md`](efg-library-computability-declarations.md)
的算法机会补充。具体方法、owner、状态和实施顺序记录在
[算法实现台账](efg-algorithm-implementation-ledger.md)。Lean 源码和已有
correctness 定理仍是实现状态的权威。

## 1. 结论

“有限”与“可计算”、“无限”与“不可计算”都不能画等号。

1. 一个问题即使只有有限时界，只要它仍以任意 `Measure`、任意可测核、任意
   `ℝ` 函数或不可判定事件为输入，就没有得到算法。
2. 一个问题即使描述无限路径，只要输出契约是“给定任意有限时界，返回精确前缀
   律”，或者过程有可执行的吸收、折扣、自动机或误差结构，就可以有算法。
3. 当前 58 个原声明仍保留分析签名。本审计没有发现可以直接宣称“原签名已被算法
   等价替换”的新声明；这也不是 58 个数学不可计算性定理。
4. 主库已经覆盖有限律 `map`/`bind`、有限 profile-law、有限抽象动作 realization、
   chance presentation 与显式 effective kernel profile 的离散编译、绝对时钟有限前缀及其投影一致性、有界终止
   完整事件路径重放、续局截断中心／半径／最小时界搜索、有限前缀有理收益、有限纯
   Nash 枚举，scheme center/radius/interval 搜索，以及允许非终止闭类的有限有理
   Markov reachability、零收益边界、精确折扣 Bellman、终止时有限 monitor product，
   以及无限 min-parity BSCC 分类到两终点首达问题的精确归约。
5. 对明确给出有限律、终点判定和局部表示证书的 effective 子域，58 项中的有限编译
   主路线现已全部有核心实现；S130 的高层 adapter 也已落地。任意原
   `KernelBehavioralProfile` 不会因此自动获得可枚举支持。tail event/state 与两条
   高层 state-path、continuation event/state、fresh restart、normalized continuation
   及正质量 conditional tail 的逐 horizon 直桥已经补齐；continuation utility 的
   原分析直桥仍需终点一致与可算尾界。这一缺口不能用有限边缘定理冒充已关闭。
6. 仍有一组真正的无限算法机会：惰性前缀采样、一般有效路径上的折扣收益和有限状态
   safety/ω-regular 目标。一致柱事件接口、有限 Markov reachability、有限有理 Markov
   折扣值、终止时 monitor、min-parity BSCC 归约，以及选定事件／simple-observable
   语言上的有效非原子 law/map/kernel 查询已经落地；一般 safety、其他自动机约定、
   原链解析 ω-event 桥、任意可测集和任意可积函数仍无统一算法。
7. 用互斥的主要处理路线统计，58 项恰好分为：已有有限核心路线 34 项、无限在线
   表示路线 18 项、认证近似路线 5 项、待补有限编译 0 项、原路径级障碍 1 项。

## 2. 标记

| 标记 | 严格含义 |
|---|---|
| `F✓` | 对应的有限有效子问题已有主库可执行核心；不表示原 `Measure`/`Kernel` 返回值可编译 |
| `F+` | 有明确有限算法，但对应的通用主库 owner 或 correctness bridge 尚未完成 |
| `∞✓` | 已有算法统一回答任意有限时界，或已有受证明的无限时域精确算法 |
| `∞+` | 无限问题在额外有效结构下有算法，但当前主库没有该通用接口或证明 |
| `≈✓` | 在行内明确的有效表示与 certificate 子域上，已有任意正精度算法及真实误差证明；不表示任意分析对象会自动给出 certificate |
| `≈+` | 可返回任意正精度的有证书近似；不是精确原值替换 |
| `Σ₁*` | 在表中明确写出的受限定义域上，成功见证可以搜索；不表示原谓词可半判定 |
| `G` | 原签名／输出契约仍在分析层，尚无已验证的同签名可编译替换；原因可能是非有效输入、分析输出或经典分支 |
| `×` | 对原全域契约有明确障碍；只用于已给出反例或不可识别性论证的情形 |

58 行的原签名标记一律是 `G`；逐项表为避免重复，只列子域机会标记。这是接口判断，
不是不可能性定理。`F✓` 和 `∞✓` 只评价准确写出的有效子域及输出表示。`×` 只额外
标记已知的全域数学障碍。

互斥的主要路线用于确认没有漏项；逐项表中的机会标记可以重叠：

| 主要路线 | 数量 | 声明 |
|---|---:|---|
| 已有有限核心 `E` | 34 | S082--S088、S102--S105、S107--S109、S111--S117、S119--S124、S127--S130、S135--S136、S138 |
| 无限在线表示 `O` | 18 | S081、S089、S092--S097、S106、S110、S118、S125--S126、S131--S134、S137 |
| 认证近似 `A` | 5 | S090--S091、S098、S100--S101 |
| 待补有限编译 `F` | 0 | — |
| 原路径级障碍 `X` | 1 | S099 |

## 3. S081--S138 逐项标记

### 3.1 策略律和一般路径语义

| ID | 声明 | 标记 | 数学判断 |
|---|---|---|---|
| S081 | `kernelBehavioralCompletePathLawSemantics` | `F✓`, `∞✓`, `∞+` | A20 已在显式 effective presentation/profile 与局部 weighted-Dirac 表示证书下编译高层 kernel profile，并给 coherent 全 horizon event-prefix law 及每个有限边缘的 `partialTraj` 等式。它只特化到 discrete complete-history model，且没有构造本声明所需的完整 state-path Measure 或 a.e. lawful 证书；一般 `CompletePathLawSemantics` 继续是分析数据。 |

### 3.2 条件续局、时钟和路径收益

| ID | 声明 | 标记 | 数学判断 |
|---|---|---|---|
| S088 | `conditionalTailKernel` | `F✓`, `∞+`, `×` | 正质量有限 observation 用 Bayes 归一化精确可算；在原解析 prefix 单点质量非零、满足 RCD 所需标准 Borel／单点可测假设时，`measure_tailPrefixLawFrom_eq_conditionalTailKernel_apply_map_frestrictLe_of_prefix_ne_zero` 已把 effective tail-prefix law 的任意有限边缘直连原 kernel 点值。连续情形还需可计算联合／边缘密度、有效积分与尾界或直接 conditional-density 构造；零质量版本不由联合律唯一决定，库没有替它选择版本。 |
| S089 | `continuationTailKernel` | `F✓`, `∞✓` | 对每个未来时界保留完整绝对前缀和绝对时钟递归；`measure_tailPrefixLawFrom_eq_continuationTailKernel_apply_map_frestrictLe` 已证明有效 tail-prefix law 精确等于本原 kernel 在该 prefix 的逐有限边缘。它不构造可执行的无限路径 kernel。 |
| S090 | `BoundedPathUtility.continuationExpectedUtility` | `F✓`, `∞✓`, `≈✓`, `∞+` | `EffectivePathUtility` 已精确计算因子化于指定有限 prefix 的有理期望；`ContinuationTruncation` 已计算绝对时钟续局的中心与 `B·q_H` 半径，`DiscountedPathUtility` 则给一般 coherent path 的几何尾算法。`Simulation.Kernel.CertifiedPathApproximation` 现已在任意精确 finite-marginal correspondence 下，从逐路径 uniform certificate 推出真实分析期望落入 scheme interval，且成功搜索的误差不超过 tolerance。原任意有界可测 utility 不会自动产生 prefix approximant 或 uniform／`L¹` 模数。 |
| S091 | `continuationExpectedEventualUtility` | `F✓`, `F+`, `≈+` | 绝对前缀续局的未完成质量、停止中心、半径、有预算首个时界和存在性驱动的最小时界搜索均已实现。仍需证明 supplied finite-horizon payoff 与原 eventual utility 在终点上一致，并把原几乎必达证明转成 `B·q_H → 0` 的直接分析桥；`ε=0` 不在搜索保证内。 |
| S092 | `continuationEventPathMeasure` | `F✓`, `∞✓` | A20 在 discrete complete-history representation 下把显式 effective high-level profile 编译成 raw event policy；从完整 canonical prefix 按绝对时钟执行后再作 tail reindex。`effective_measure_tailPrefixLawFrom_eq_continuationEventPathMeasure_map_frestrictLe` 已把每个有限 event-prefix 直连本原 Measure 的边缘；一般 model 的无限 Measure 仍由分析声明承担。 |
| S093 | `continuationStatePathMeasure` | `F✓`, `∞✓` | 在 S092 的完整 event/action history 执行完成后才投影状态；`effective_measure_tailPrefixLawFrom_map_states_eq_continuationStatePathMeasure_map_frestrictLe` 已直连原 state-path Measure 的每个有限边缘，不会提前删除影响未来策略的 action occurrence。 |
| S094 | `freshRestartStatePathMeasure` | `F✓`, `∞✓` | A20 在 discrete complete-history representation 中从 continuation root 以时间零执行 effective profile，再投影状态。`effective_measure_finitePrefixLawFrom_map_states_eq_freshRestartStatePathMeasure_map_frestrictLe` 已给逐 horizon 精确等式；它没有把 fresh restart 与绝对时钟续局混同，也不构造完整无限 Measure。 |
| S095 | `absolutePathMeasureFromPrefix` | `F✓`, `∞✓` | `absolutePrefixLawFrom` 对旧前缀内和前缀后的任意绝对 horizon 都可查询；`effectivePathLawFrom` 另把 post-start 查询打包为以 `FiniteLaw.Equivalent` 表达截断一致性的 projective family，并逐 horizon 对接 `partialTraj`。这仍不是原完整路径 `Measure` 的可执行值。 |
| S096 | `tailEventPathMeasureFromPrefix` | `F✓`, `∞✓` | 先按绝对时钟执行到有限时界，再作有限 reindex，即可计算任意尾事件前缀；`measure_tailPrefixLawFrom_eq_tailEventPathMeasureFromPrefix_map_frestrictLe` 已直连原 tail Measure 的每个有限边缘，但不声称完整 infinite Measure 等式。 |
| S097 | `tailStatePathMeasureFromPrefix` | `F✓`, `∞✓` | 对 S096 的完整事件历史结果作状态投影；`measure_tailPrefixLawFrom_map_states_eq_tailStatePathMeasureFromPrefix_map_frestrictLe` 已直连原 state-tail Measure 的每个有限边缘，执行前不会丢掉影响策略的 action occurrence。 |

### 3.3 最终收益和一般积分

| ID | 声明 | 标记 | 数学判断 |
|---|---|---|---|
| S098 | `BoundedPathUtility.expectedUtility` | `F✓`, `∞✓`, `≈✓`, `∞+` | coherent prefix law 上的有理 cylinder utility 已用 `expectRat` 实现，并证明延长 horizon 不改变旧 observable 的期望；`DiscountedPathUtility` 给出一般 coherent path 的几何尾算法，有限有理 Markov chain 还可直接精确求无限折扣 Bellman 值。新的 A15 语义叶先把 lifted prefix integral 识别为精确有理 center，再由逐路径 uniform bound 推出原分析积分位于区间及搜索误差；单独的有界性和可积性仍不提供这一证书。 |
| S099 | `eventualUtility` | `F✓`, `Σ₁*`, `×` | 给定停止时界时 `stoppedUtility` 可算。只有在路径坐标可生成、终点可判定且“合法并终点吸收”的受限域上，第一次终止才可半搜索；返回收益还要求 payoff 有效。原 raw-path 谓词是 `Σ⁰₂` 形状，不能由固定有限前缀决定。 |
| S100 | `expectedEventualUtility` | `F✓`, `F+`, `∞✓`, `≈+` | 有限有理链现已允许非终止闭类：`canReachTerminal` 剪去不可达终点区，`solveReachable` 精确解有理方程，`zeroOnNonhitReward` 把永不命中贡献定为 0；`outcomeLaw` 精确返回 `FiniteLaw (Option Terminal)`。`lateHitMass H = (Q^H p)_i` 排除永久不终止质量、趋于 0，并给零收益边界截断余项。仍缺把一般 EFG 编译到该 chain 及直连原积分的桥；非 Markov 的几乎必达有限执行可用续局截断搜索作正容差估计。 |
| S101 | `PathUtility.expectedUtility` | `F✓`, `∞✓`, `≈✓` | finite-prefix 有理观测、certified approximation、折扣 scheme 和有限链精确解均已存在。A19 进一步对表示原 state-path Measure 的 `EffectiveLaw` 计算有限有理 `SimpleObservable` expectation oracle；调用者给出该 observable `Denotes` 玩家 utility 的证明后，EFG bridge 证明 oracle 表示原 `expectedUtility`。任意 `Measurable`／`Integrable` 证明仍不会自动构造事件码、有限 observable 或误差模数。 |
| S102 | `unfinishedMass` | `F✓`, `F+`, `∞✓` | raw policy 在任意时界的未终止质量已可精确累加，续局版本也已有中心／半径／搜索；高层 kernel profile wrapper 的直接 API/bridge 尚缺。有限有理 Markov 链现可分别精确计算最终命中、不终止和 late-hit，即使存在非终止闭类。 |

### 3.4 一步核、历史执行和完整路径

| ID | 声明 | 标记 | 数学判断 |
|---|---|---|---|
| S103 | `KernelArena.toMeasurable` | `F✓` | `KernelArena.next` 已是有限精确算法；`toMeasurable` 只把结果改成分析表示。 |
| S104 | `EventHistoryActionPolicy.actionStepKernel` | `F✓` | 有限动作律 bind 有限转移律，再记录实际动作；已有一步 correctness。 |
| S105 | `EventHistoryActionPolicy.coordinateMeasure` | `F✓`, `∞✓` | 运行到请求坐标再投影即可；已有任意坐标桥接。 |
| S106 | `EventHistoryActionPolicy.pathMeasure` | `F✓`, `∞✓` | 一般有效 policy 已有对全部 horizon 一致的事件前缀查询。有统一正支持终止界时，`FiniteCompleteEventPath.law` 还会把界时 event prefix 重放成终点吸收的 `FiniteLaw (ℕ → PathEvent)`，并证明合法性、终止吸收及所有 post-start 有限边缘。分析桥只证明这些有限边缘等于 `partialTraj`，没有证明该有限 Dirac 测度等于原无限 `pathMeasure`。 |
| S107 | `EventHistoryActionPolicy.pathStepKernel` | `F✓` | 可判定终止后，终点 pure 吸收、非终点调用 S104。 |
| S108 | `EventHistoryActionPolicy.prefixMeasure` | `F✓`, `∞✓` | 任意有限事件前缀律和分析等式均已实现。 |
| S109 | `EventHistoryActionPolicy.stateCoordinateMeasure` | `F✓`, `∞✓` | 事件执行后作状态坐标投影；已有分析等式。 |
| S110 | `EventHistoryActionPolicy.statePathMeasure` | `F✓`, `∞✓` | 所有有限状态柱与坐标查询已有；在 A09 的有界终止子域上，`FiniteCompleteEventPath.stateLaw` 把完整事件路径有限律逐坐标投影成有限支持完整状态路径律，`stateLaw_prefix_all` 证明任意有限状态前缀正确。现有分析桥仍只覆盖有限边缘，不是原无限 state-path `Measure` 的整体等式。 |
| S111 | `recordedTransition` | `F✓` | 在有限转移律上 `map` 为“所选动作、后继状态”对，已由 `HistoryKernel` 覆盖。 |
| S112 | `KernelArena.Policy.toMeasurable` | `F✓` | 有效策略本身已有；分析 policy 只是 finite-law 到核的包装。终止测试必须显式可判定。 |
| S113 | `KernelArena.Policy.toMeasurableKernel` | `F✓` | `Option`/终止分支可表达终点无动作，非终点保留原有限动作律。 |
| S114 | `ActionPolicy.actionStepKernel` | `F✓` | 有限动作与转移的 bind 已由 `KernelArena.stepLaw` 实现。 |
| S115 | `ActionPolicy.stepKernel` | `F✓` | 有终止判定时，terminal pure 与非终点 stepLaw 都可执行。 |
| S116 | `HistoryActionPolicy.actionStepKernel` | `F✓` | 保留完整状态历史后作有限 bind，已实现。 |
| S117 | `HistoryActionPolicy.coordinateMeasure` | `F✓`, `∞✓` | 对任意时界执行完整历史后投影坐标，已有桥接。 |
| S118 | `HistoryActionPolicy.pathMeasure` | `F✓`, `∞✓` | `StateEffectivePathLawFrom` 已给全时界一致状态前缀族和逐 horizon 分析边缘等式；有界终止时可先用 `toEventHistoryPolicy` 保留动作 occurrence、应用 A09，再投影状态得到有限支持完整状态路径律。仍未宣称该结果与原无限 `pathMeasure` 作为 Measure 整体相等。 |
| S119 | `HistoryActionPolicy.pathStepKernel` | `F✓` | 可判定最新状态是否终止后执行有限一步。 |
| S120 | `HistoryActionPolicy.prefixMeasure` | `F✓`, `∞✓` | 任意有限状态前缀律和 `partialTraj` 等式已实现。 |
| S121 | `RealizedActionPolicy.realizedKernel` | `F✓` | `EventInformation.RealizedActionPolicy.realizedActionLaw` 已对有限抽象律与依赖完整 event prefix 的有限 realization 作 `bind`，再记录具体 action；dependent action fiber 从类型上保证状态合法性。`realizedKernel_eq_measure_realizedBundleLaw` 在显式局部表示条件下证明 weighted-Dirac 等式；逐输出有限不等于输入依赖自动可测。 |
| S122 | `RealizedActionPolicy.toEventHistoryActionPolicy` | `F✓` | `toEventHistoryPolicy` 已把 S121 编译成 ordinary action-recording executor；`toEventHistoryPolicy_analyticallyRealizedBy` 同时覆盖终点零质量和非终点有限律。A06 本身不会自动编译任意高层 profile；A20 通过显式 effective presentation/profile 与表示证书复用它关闭 S130 的有效子域。 |
| S123 | `ActionPolicy.pathStepKernel` | `F✓` | 从前缀读取最新状态后复用 S115；没有独立的概率难题。 |

### 3.5 Presentation 与 restart

| ID | 声明 | 标记 | 数学判断 |
|---|---|---|---|
| S124 | `ObservedChanceGame.MeasurablePresentation.compiledPolicy` | `F✓` | `BehavioralProfile.toFiniteEventPolicy` 已直接读取原 player/chance `FiniteLaw` 并记录实际 action，不执行任意分析 realization kernel；`compiledPolicy_kernel_eq_finiteActionLaw?` 和 `toFiniteEventPolicy_analyticallyRealizedBy` 在显式终点判定下证明与原 `compiledPolicy` 的局部等式。 |
| S125 | `ObservedChanceGame.MeasurablePresentation.eventPathMeasure` | `F✓`, `∞✓`, `∞+` | A07 已证明 direct finite policy 的任意 bounded event-prefix law 等于原 `compiledPolicy` 的 `partialTraj`；A08 给一致的全 horizon 查询，若另给统一正支持终止界，A09 构造有限支持完整事件路径律。尚无把这组有限边缘提升成与原无限 `eventPathMeasure` 整体相等的 Lean 定理，也没有任意 Borel 事件求值器。 |
| S126 | `ObservedChanceGame.MeasurablePresentation.statePathMeasure` | `F✓`, `∞✓`, `∞+` | `measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe` 已证明 direct event execution 在保留完整 action history 后投影所得的任意整段 state-prefix，等于原 `statePathMeasure` 的相应有限边缘；有界终止时还可投影 A09 的完整路径有限律。一般非原子 presentation 和原无限 state-path Measure 整体等式仍在分析层。 |
| S127 | `ObservedChanceGame.MeasurableHistoryModel.discrete` | `F✓` | 历史追加和确定性单原子转移已经可计算；不可执行部分只是测度包装。 |
| S128 | `ObservedGame.MeasurableHistoryModel.discrete` | `F✓` | 与 S127 相同，是既有离散历史模型的分析 lift。 |
| S129 | `ObservedChanceGame.AnalyticHistoryArena` | `F✓` | 计算对象是现有 `historyKernelArena`；该别名只选择分析表示。 |
| S130 | `KernelBehavioralProfile.compiledPolicy` | `F✓` | `EffectiveKernelPresentation` 与 `EffectiveKernelBehavioralProfile` 已显式携带 information、有限抽象律、prefix-dependent finite realization、终点判定和 chance law，并沿 A06 编译；`effective_compiledPolicy_analyticallyRealizedBy` 在 measurable abstract-action equivalence、两级 weighted-Dirac 表示条件和 discrete complete-history model 下直连原 high-level `compiledPolicy`。任意一般 profile 仍不能自动枚举支持。 |
| S131 | `KernelBehavioralProfile.eventPathMeasure` | `F✓`, `∞✓`, `∞+` | A20 已给 effective high-level profile 的 bounded event-prefix law、coherent 全 horizon family，以及在 discrete complete-history model 上逐 finite prefix 等于原 `compiledPolicy` 的 `partialTraj`。尚未把有限边缘提升为原无限 `eventPathMeasure` 的整体 Measure 等式，也没有任意 Borel event evaluator。 |
| S132 | `KernelBehavioralProfile.statePathMeasure` | `F✓`, `∞✓`, `∞+` | `effective_measure_finitePrefixLawFrom_map_states_eq_statePathMeasure_map_frestrictLe` 已在 A20 representation 与 discrete complete-history model 下证明：先执行完整 event/action history，再投影所得的任意整段 state-prefix 等于原 `statePathMeasure` 的有限边缘。一般 model 与完整 infinite Measure 整体等式仍在分析层。 |
| S133 | `freshRestartEventPathMeasure` | `F✓`, `∞✓`, `∞+` | A20 已在 discrete complete-history model 上把 explicit effective high-level profile 编译成 raw policy，因而可复用 fresh finite-prefix executor；有界终止后还可复用 A09 的完整事件路径重放。尚无一般 model 或与原完整 restart Measure 的整体等式，也没有任意路径事件求值器。 |
| S134 | `normalizedContinuationEventPathMeasure` | `F✓`, `∞✓`, `∞+` | `effective_measure_normalizedTailPrefixLawFrom_eq_normalizedContinuationEventPathMeasure_map_frestrictLe` 已在 A20 representation 与 discrete complete-history model 下实现：保留 canonical 完整 event prefix 和绝对时钟执行，tail reindex 后只把坐标零改成同状态 initial marker，并逐 horizon 直连原 normalized Measure。一般 model 与原无限 Measure 整体等式仍在分析层。 |
| S135 | `absoluteFinitePrefixMeasureFromPrefix` | `F✓` | 已有对任意 horizon 的精确 `FiniteLaw` 与原测度等式。 |
| S136 | `freshRestartFinitePrefixMeasure` | `F✓` | 已有时间零 fresh 递归算法与原测度等式。 |
| S137 | `splicedFreshAbsolutePathMeasure` | `∞✓`, `F+` | 任意有限拼接前缀已有；有界终止时可复用 A09 的完整事件路径律并作确定性 splice，得到有限支持完整拼接路径。尚缺该完整路径 wrapper 及与原 spliced Measure 的整体桥。 |
| S138 | `splicedFreshFinitePrefixMeasure` | `F✓` | 已有对任意 horizon 的精确算法与原测度等式。 |

## 4. 有限算法的已实现范围和剩余缺口

### 4.1 finite profile、realization 与 effective presentation

S082、S085、S086 已有稳定 owner
`FinitePureProfileLaw := FiniteLaw G.PureProfile`。坐标、outcome 和完整路径分别用同一个
`FiniteLaw.map` 实现，并逐项证明 weighted-Dirac 解释等于原分析 marginal／pushforward。
这里的 path 算法可以返回有限支持的无限 `CompletePlay` 原子；它没有把任意非原子
profile measure 变成可执行对象。

S121--S122 已按

```text
abstractLaw.bind (realizationLaw time prefix)
```

实现。realization 可以随机并依赖完整 event prefix；返回 dependent action fiber，因而
无需另做状态相等判定。分析桥要求调用者给出 analytic information、realization、
policy，以及抽象／具体局部 kernel 的有限 Dirac 表示条件。这个要求是实质性的：每个
输入点都返回有限支持律，并不能推出输入到测度的函数可测。

S124 的特例也已实现。算法直接读取行为 profile 与 chance 的原 `FiniteLaw`，用显式
终点判定装配 action-recording event policy；原 `MeasurablePresentation` 仅为局部等式
和所有有限 event-prefix correctness 提供证明。

A20 已完成 S130 的有效子域。`EffectiveKernelPresentation` 显式拥有 information、
prefix-dependent finite realization、终点判定、chance classifier 和具体 chance law；
`EffectiveKernelBehavioralProfile` 提供有限抽象律及 realized chance compatibility，沿
S121--S122 生成 raw event policy、bounded prefix law 和 coherent effective path law。
算法输入没有预先编译的具体 policy 或 path law。

语义叶的 `AnalyticRepresentation` 要求 abstract-action measurable equivalence，以及
抽象 kernel 与 realization kernel 的两级 weighted-Dirac 表示。由此先证明 raw
`compiledPolicy` correspondence，再证明任意 finite event-prefix 等于 `partialTraj`，
并特化到原 high-level `KernelBehavioralProfile` 的 discrete complete-history model。
它没有从任意一般 profile 自动枚举支持，不覆盖任意 measurable-history model，也不
构造 infinite path Measure。

### 4.2 `KernelArena` 的有界终止完整事件路径

`FiniteCompleteEventPath.law` 已实现随机转移 `KernelArena` 的构造：先执行到给定
`steps`，再把每个有限 event prefix 重放为终点吸收的 `ℕ → PathEvent`。构造本身总能
执行；`PositiveSupportTerminates` 是证明该有限律确实由合法、在界时终止且此后吸收的
路径组成的前提。

`law_prefix_all` 对任意 `querySteps` 证明重放律的 post-start prefix 边缘等价于继续
执行得到的 `prefixLawFrom`，包括查询超过终止界的情形。语义叶进一步证明这些
post-start event-prefix、event-coordinate 和 state-coordinate 边缘等于已有 analytic
`partialTraj`。它没有证明 weighted-Dirac complete-path measure 与原 `Kernel.traj`
在无限函数空间上整体相等，也没有给任意 Borel／tail event 求值器。

`FiniteCompleteEventPath.stateLaw` 已把完整 event path 投影成完整 state path，且
`stateLaw_prefix_all` 对任意有限状态前缀证明与直接 action-recording execution 后的
状态投影一致。S126 与 S132 现已有各自的 direct finite-prefix 分析桥；这些有限边缘
等式仍不能误报成整个 state-path Measure 等式。

### 4.3 续局截断、有限前缀 utility 与 scheme 搜索

`ContinuationTruncation` 已从任意绝对 `start` 和完整初始 prefix 实现：

- 精确未完成质量 `q_H`、停止中心和半径 `B q_H`；
- 有预算的首个 horizon 搜索及 soundness、minimality、`none` 当且仅当；
- 在另给存在性证明时由 `Nat.find` 得到全局最小 horizon；
- state execution 与记录 action 后的 event execution 之间的中心、半径和区间保持。

`EffectivePathUtility` 已在 coherent state/event prefix family 上实现有理柱函数的精确
`expectRat`，并证明把较早 observable 提升到较晚 horizon 后期望不变。它保留完整
event action occurrence，并显式证明忘记 action 后的 state observable 对应。

`CertifiedPathApproximation` 在此基础上接收“每个 horizon 的可执行有理 observable
与非负有理 radius”，计算精确 center、`[center-radius, center+radius]` scheme
interval，并实现预算内第一个可接受 horizon、失败当且仅当所有已测试 radius 都超过
tolerance、minimality 和显式存在性驱动的最小 horizon。`Vanishes` 只保证每个正
tolerance 存在可接受时界；它不提供外部目标。

因此 A15 的运行 interval 仍只由 scheme 自身定义，也不接受 target expectation
作为输入。独立的 `Simulation/Kernel/CertifiedPathApproximation` 语义叶现在接收
exact finite marginals、外部 utility 的 measurable/integrable 证明、lifted observable
的 measurability，以及逐路径 uniform approximation certificate。它先证明 prefix
integral 等于算法 center，再推出目标期望落入 interval，并证明成功搜索的真实误差
不超过 tolerance。任意分析 `PathUtility.expectedUtility` 不会仅凭 measurable／
integrable 自动满足这些额外条件；`L¹` certificate 版本也尚未提供。

这些是 A10/A14/A15 的运行核心。A15 已能消费真实 uniform certificate，但不会自动
证明某个原 `BoundedPathUtility` 或 `eventualUtility` 与 supplied horizon payoff 满足
终点一致、统一界和截断误差。因此 S091、S100 的 eventual-utility 直桥仍需额外
analytic realization、utility factorization 和几乎必达条件；`ε = 0` 也不由正容差
搜索保证。

### 4.4 可含非终止闭类的有限有理 Markov 求解

`FiniteMarkovChain.Reachability` 已去掉全链吸收前提。它从正概率图计算
`canReachTerminal`，将不可达终点区的后续质量剪为 0，并在可达区解
`(I - Q_reachable) x = b`。语义层证明行列式非零、方程正确、解唯一及 Bellman
unroll，因而闭合非终止类不会造成奇异的待解自由度。

同一 solver 已精确给出：

- 最终命中任意终点及各指定终点的概率；
- `FiniteLaw (Option Terminal)`，其中 `none` 恰为不终止概率；
- 永不命中取 0 的 terminal reward；
- 每个有限时刻的 first-hit 系数及其无穷和；
- `lateHitMass H = (Q^H p)_i`、其趋零定理和
  `B * lateHitMass H` 的 reward 余项界。

`lateHitMass` 不是 survival：进入永久非终止闭类的质量不会计入它，所以即使
nontermination probability 为正，它仍趋于 0。完整 `(hitTime, terminal)` 联合分布
可能有可数无限支撑，仍以 first-hit 查询／级数表示，不能伪装成 `FiniteLaw`。

尚未实现的是一般 EFG 到该有限 chain 的编译、无条件命中时间在 `ℚ ∪ {∞}` 中的统一
接口，以及与 S100 原 `expectedEventualUtility` 积分的直接桥。这些缺口不影响上述
有限有理 Markov 结果本身的精确性。

### 4.5 任意有限有理 chain 的精确折扣值

`FiniteMarkovChain.Discounted` 已对任意有限有理 chain、有理
`0 ≤ γ < 1` 及 transient-state reward `r : Fin n → ℚ` 实现

```text
(I - γQ) v = r.
```

算法先用 Bool 检查 discount，再由 Cramer 公式计算 `v`；调用者不提供逆矩阵或
行列式证书。最大绝对坐标收缩论证证明 `I-γQ` 单射和行列式非零，因此结果满足且唯一
满足 Bellman 方程 `v = r + γQv`。reward 在原 terminal 首次命中后为零；这不是给
terminal 自环持续发放 reward 的总状态模型。该证明只用每个 `Q` 行和至多 1，不要求
链最终吸收，所以非终止闭类在 `γ<1` 下没有额外障碍。

有限 horizon 值精确累加时刻 `0,...,H-1` 的 reward，Bellman unroll 给出余项
`(γQ)^H v`。若 `|r_i| ≤ B`，库已证明

```text
|v_i - v_i^(H)| ≤ B * γ^H / (1 - γ).
```

这是有限 Markov 子域的精确无限时域算法。它尚未把一般 EFG 历史过程编译成有限
Markov state，也没有把任意 path utility 识别成该逐状态折扣 reward。

## 5. 可以实现的无限问题

### 5.1 一致柱事件接口

对有效一步有限律，

```text
horizon ↦ FiniteLaw (Prefix horizon)
```

是一个总算法，即使总状态载体和可能运行长度无限，只要每步实际返回可遍历的有限律
并且所需状态操作可执行。`StateEffectivePathLawFrom` 和
`EventEffectivePathLawFrom` 已把它作为无限路径的有效查询表示。bundle 本身记录：

- 零时界初值；
- 任意早晚时界的截断边缘一致性；
- 任意有限 prefix 上的精确 Boolean cylinder mass 和坐标律。

`prefixLawFrom` 提供具体计算，coherence 使用 `FiniteLaw.Equivalent` 而非原子列表
相等，因为未来分支会把同一旧 prefix 拆成多个重复原子。`EffectivePathLaw` 的分析叶
逐时界对接 `partialTraj`；由 stopped-step executor 构造的 family 另继承终点吸收，
restart bridge 覆盖 fresh/splice 查询。这些 bundle 是
专门的 cylinder/prefix 接口，不是声称任意 `Measure` 都带算法的通用
`ComputableEFG` 字段。

在有限字母的 Cantor 路径空间上，
[Hoyrup--Rojas, Corollary 4.2.1](https://arxiv.org/pdf/0709.0907)
给出“测度可计算当且仅当所有有限柱质量统一可计算”。因此一致的有限有理前缀律
确实是完整无限路径测度的有效表示，不要求路径终止。对一般无限 Lean 状态载体，
要进一步称为 computable Borel measure，还必须给状态空间的有效编码或 computable
Polish 表示；单有一个类型和 `MeasurableSpace` 不够。

可再提供 `randomBits → horizon → Prefix` 的惰性采样器。一般有理概率的 rejection
sampler 只保证对随机比特几乎处处终止，不能承诺对每条无限 bit stream 都终止；
总定义采样器的边界见
[Ackerman--Freer--Roy, Lemma 2.13](https://cfreer.org/papers/AckermanFreerRoyCompCondProb.pdf)。
柱事件质量可精确计算也不意味着任意路径事件可精确计算：有效 open reachability
通常只下半可计算，closed safety 通常只上半可计算，任意 Borel 事件没有统一求值器。

### 5.2 有限状态有理链的无限时域算法

固定有限状态、有限动作、固定策略和有理转移后，主库现已用有限图 reachability 与
有理线性方程精确计算：

- 最终到达终点的概率；
- 各终点类型的最终概率及 `FiniteLaw (Option Terminal)`；
- 每个时间／终点的首达系数 `(Q^r R)_{ia}`；
- 永不终止时取零的有界终端收益期望；
- 逐起点的最终命中概率、是否可达及是否几乎必达。
- 确定性终止时 monitor product 的接受概率和显式不终止质量；
- 自动正支持 reachability/SCC/BSCC 分类后，两终点归约链的接受与拒绝首达概率。

完整首达时间联合律可能有可数无限支撑，应以系数查询或生成表示返回，不能称为
`FiniteLaw`。主库 `FiniteMarkovChain.autoCheck/autoSolve` 覆盖全域吸收时的首达
收益与时间；`Reachability` 则通过可达区剪枝去掉最终命中概率和 zero-on-nonhit
reward 的“全链吸收”限制。

无条件命中时间的统一 `ℚ ∪ {∞}` 输出仍未实现：可进入非目标闭类时它是 `∞`，从
给定起点几乎必达时才是有限有理数。终止时有限 monitor 与无限 min-parity 已由
`Automaton`、`Parity` 覆盖；一般 safety 及其他目标语言仍待实现。折扣 reward 已由
第 4.5 节的 solver 覆盖。
有限状态本身仍不够：若转移和收益是任意 Lean `ℝ`，精确零测试和大小比较未必可算；
需要有理数、代数数或明确的可计算实数接口。

### 5.3 折扣收益和有效连续路径收益

若 `|r_t| ≤ B` 且折扣 `0 ≤ γ < 1` 有有效表示，并给出可执行的严格间隙证书，
则保留时刻 `0,...,H-1` 后的尾误差有显式界

```text
B * γ^H / (1 - γ).
```

现有 `EffectivePathUtility` 已提供每个有限 cylinder center 的精确有理期望及 horizon
invariance；`DiscountedPathUtility` 把一般 coherent state/event path law、绝对起点、
有理逐期 reward、`γ < 1` 和统一界 `B` 组装为 A15 scheme。reward 的时间参数使用
绝对时刻 `start+k`，折扣指数则按续局价值约定从 supplied start 重新以 `γ^k` 计；它精确计算前 `H` 项，证明
几何 radius 消失，并计算满足任意正有理 tolerance 的最小时界。该纯算法层仍不把
外部无限级数或其积分作为运行输入；说明这个 radius 确实控制某个外部分析 utility
需要独立的 uniform 或 `L¹` 证书。A15 语义叶已经实现 state-path 的 pointwise
uniform 版本；event-path 与纯 `L¹` 版本仍按消费者需要扩展。

有限有理 Markov 链的 `Q`、`r`、`γ` 情形则已由 `FiniteMarkovChain.Discounted`
精确完成：`r : Fin n → ℚ` 只在原 transient 状态计入，首次命中原 terminal 后贡献
为零；solver 解 `v = r + γQv`，证明唯一性、有限 unroll 和上述尾界，而且不要求最终
吸收。若需要 terminal 自环上的持续 reward，必须先改用总状态 reward 模型。若 `γ`
只是 computable real，则仍只能按其数值表示近似。更一般地，路径收益能被有限柱函数
一致逼近且给出可执行模数时，现有 uniform certificate 已能把算法 center 接到分析
积分；纯 `L¹` certificate 尚未实现。

### 5.4 Reachability、safety 与 ω-regular 目标

对有限状态有理 Markov 链，`Automaton` 已实现确定性终止时 monitor product；
`Parity` 把原终止态改成永久自环，自动计算正支持 reachability、SCC、bottom SCC，
按“component 最小 priority 为偶数”的 min-parity 约定分类，并把 accepting/rejecting
bottom 类约化成两终点链。库内证明约化链必吸收、Bellman 矩阵非奇异、接受与拒绝
概率唯一且和为 1，并把两个结果分别识别为归约链的 `terminalProbability 0/1`。
闭集 reachability 当前为指数级，Leibniz/Cramer 算术最坏为阶乘级。

这些结果闭合了有限 Markov 图到两终点归约链的首达语义；当前尚未证明原总链几乎
必然进入底 SCC、底 SCC 内有关状态几乎必然无限常返，也未证明所得有理数等于
Mathlib 路径 `Measure` 上的 ω-parity 事件概率。一般有限 MDP、随机博弈和 safety
solver 也尚未由这个 Markov-chain 结果自动获得。

这条路线只能覆盖带有限自动机描述的路径事件。任意可测集合不是有限自动机输入；
部分可观测、无限状态或多玩家一般随机博弈的可判定性也不能从有限状态 Markov 结论
外推。

### 5.5 有效非原子概率

非原子不等于不可计算。A19 现已提供通用的选定语言接口：`RatOracle` 对每个正有理
tolerance 返回有理 enclosure；`EffectiveLaw` 回答事件码质量；有限有理
`SimpleObservable` 由常量、事件指标、加法和有理缩放组成；`EffectiveMap` 用逆像
编译 pushforward；`EffectiveKernel` 用 observable pullback 表示，因此 law bind 和
kernel composition 仍是可执行结构递归。纯聚合 `Effective` 不导入 Measure、Kernel
或积分；`Effective.Analytic` 才导入 proof-only `Denotes`／`Represents` 解释。

`UniformUnitInterval` 是首个真实非原子 backend：事件码是有限有理区间并，质量由
`RationalIntervalUnion.probability` 精确计算为 singleton enclosure，分析叶证明它
表示单位区间 volume 和常值非原子 kernel。EFG 的两项 bridge 又覆盖 S082/S085/S086
的有效推前，以及 S101 在有限 simple observable 精确表示玩家路径 utility 时的期望。

边界因此变得具体：事件语言必须对所需 preimage 和 observable pullback 封闭；一般
连续 backend 仍需自己的数值积分与误差传播算法。任意可测集合、任意可积函数和只给
Prop 性质的 `Measure`／Kernel 不是运行接口，零测前缀上的 RCD 版本也没有被 A19 选择。

## 6. 只能半判定或不能统一算法化的边界

### 6.1 有效无限 Arena 的 reachability

若目标谓词和状态相等可判定、每个状态的动作与随机后继正权重支持可有限枚举且
`next` 可执行，广度优先搜索可以在目标可达时返回一条有限历史见证。因此
reachability 是半判定的。若状态空间无限且没有有限商、良基秩或搜索界，目标不可达
时搜索可能永不停止；不能声称存在 Bool 判定器。

### 6.2 原始 `eventualUtility`

对合法终点吸收路径，第一次遇到终点即可返回收益。对 S099 接受的任意原始路径，
性质是“存在一个时刻，此后永远保持同一终端历史”；验证“此后永远”需要无限信息。
仓库的
[`LibraryFeasibility.lean`](../research/efg-computability/LibraryFeasibility.lean)
已有每个有限时界下取值 0/1 而前缀相同的实际 EFG 见证。因此原全域有限查询
求值器不可行。原谓词具有 `Σ⁰₂` 量词形状，不能把受限吸收路径上的首次命中
`Σ⁰₁` 半搜索误写为原 raw-path 谓词本身的半判定。

### 6.3 一般条件分布

有限正质量事件上的条件化是除法。连续条件化则是选择一个只在几乎处处意义下确定的
版本；在零质量 observation 上，联合律不决定唯一点值。即使联合分布本身可计算，
一般条件分布也可能不可计算。因此 S088 只能在有限原子，或可计算联合／边缘密度、
有效积分与尾界（或直接 conditional-density 构造）再加正分母下界等明确子域提供
算法。该一般反例及结构化正面条件见
[Ackerman--Freer--Roy](https://cfreer.org/papers/AckermanFreerRoyCompCondProb.pdf)。
若原子质量只是 computable real，`p > 0` 与 `p = 0` 的全域二分也未必可判定；精确
有理质量、正下界或 apartness 见证才能给全域接口。

### 6.4 一般积分

`Bounded`、`Measurable`、`Integrable` 都是数学性质，不是算法表示。若输入只给任意
Lean 函数、一般测度及这些 Prop 证明，就没有用于近似函数、测度和积分误差的可执行
信息。可计算积分必须另给有限原子、有效简单函数逼近、连续模数、折扣尾界或其他
可验证误差结构。可计算测度上的积分闭包和下半可计算边界可参见
[Hoyrup--Rojas, §4.3](https://arxiv.org/pdf/0709.0907)；仅有经典可积性并不提供
有效的 `L¹` 逼近速度。

## 7. 与均衡计算有关但不由 58 项直接暴露的机会

- 有限纯策略域、有限时界、有理收益和可判定比较下，`FinitePureNash.all` 已用
  `Finset.univ.filter` 无重复列出全部通过者，且 membership 当且仅当原 root-bound
  pure-strategy space 上的 Nash。`find` 用显式 `FinEnum PureProfile` 的有序 list 返回
  第一个，并已有 soundness、failure iff absence 和 completeness；它不从仅有的
  proposition-level finiteness 或无序 `Fintype` 经典选择一个顺序。最坏 profile 数量
  是各玩家纯策略数的乘积，每次检查还要枚举单边偏离并展开有限执行树。
- 有限完美信息树在收益比较可执行时可使用 backward induction。
- 两人零和、有限且具有完美回忆的 EFG 可以在 sequence form 上解线性规划；一般
  两人完美回忆博弈可形成 sequence-form LCP。它避免展开指数大小的 normal form，
  但仍不代表多玩家、一般和或不完美回忆博弈有同样复杂度；参见
  [Koller--Megiddo--von Stengel](https://ai.stanford.edu/~koller/Papers/Koller%2Bal%3AGEB96.pdf)。
- 有限状态折扣随机博弈、reachability/parity 随机博弈可以有数值或策略算法；必须
  分别声明玩家数、零和性、观察结构、策略记忆和误差保证。

这些应进入独立算法模块，而不是给 minimal Core 增加有限性字段。

## 8. 实现落点与仍未闭合的桥

| 状态 | owner | 已覆盖范围／仍缺口 |
|---|---|---|
| 已实现 | `Execution/Discrete/RealizedInformation.lean`；`Simulation/Kernel/FiniteRealizedInformation.lean` | S121--S122 的 dependent finite-bind compiler 与局部 analytic bridge；A20 在其上实现 S130 adapter |
| 已实现 | `Execution/Discrete/ObservedChance.lean`；`Simulation/Presentation/Chance/FiniteExecution.lean` | S124 直接 adapter、S125 任意有限 event-prefix，以及 S126 原 state-path Measure 的整段有限 state-prefix bridge |
| 已实现 | `Execution/Discrete/EffectivePathLaw.lean`；`Simulation/Kernel/EffectivePathLaw.lean` | coherent prefix/cylinder bundle、事件质量、逐 horizon `partialTraj`，以及 S096/S097 原 tail event/state Measure 的直接有限边缘；不声称完整无限 Measure 等式 |
| 已实现 | `Execution/Discrete/FiniteCompleteEventPath.lean`；`Simulation/Kernel/FiniteCompleteEventPath.lean` | 有界终止完整 event/state path、合法吸收和所有 post-start 有限边缘；不含完整路径 Measure 等式 |
| 已实现 | `Execution/Discrete/ContinuationTruncation.lean` | 绝对时钟续局的 unfinished mass、中心／半径与首个／最小正容差时界；S091 原 utility 的分析 bridge 仍缺 |
| 已实现 | `Math/Probability/FiniteMarkovChain/Reachability.lean`；`ReachabilitySemantics.lean` | 可含非终止闭类的 reachability、outcome law、zero-on-nonhit reward 和 late-hit 余项；EFG compiler 与 S100 直连桥仍缺 |
| 已实现 | `Execution/Discrete/EffectivePathUtility.lean` | coherent prefix law 上有理 cylinder utility 的精确期望与 horizon-invariance |
| 已实现 | `Execution/Discrete/CertifiedPathApproximation.lean`；`Simulation/Kernel/CertifiedPathApproximation.lean` | scheme center/radius/interval 与首个／最小 horizon 搜索；在 exact finite marginals、measurability/integrability 和逐路径 uniform certificate 下，证明外部分析 target 位于区间且成功搜索满足真实 tolerance |
| 已实现 | `Execution/Discrete/DiscountedPathUtility.lean` | 一般 coherent state/event path law 上前 `H` 项有理折扣中心、`B·γ^H/(1-γ)` 半径、消失证明、预算搜索和正容差最小时界；外部无限级数的分析解释仍由语义证书承担 |
| 已实现 | `Math/Probability/FiniteMarkovChain/Discounted.lean` | 任意有限有理 chain 上 `0≤γ<1` 的唯一精确 Bellman 解、unroll 与 `B·γ^H/(1-γ)` 界；EFG compiler 仍缺 |
| 已实现 | `Math/Probability/FiniteMarkovChain/Automaton.lean`；`Parity.lean` | 终止时确定性 monitor product；全域无限 min-parity SCC/BSCC 分类、接受／拒绝值等于两终点归约链的 `terminalProbability 0/1`；原链的底 SCC 几乎必达／无限常返和 Measure 上 ω-event 等式尚未闭合 |
| 已实现 | `Observed/FinitePureNash.lean` | `all`/`find`、soundness 与 completeness；不属于 58 项原 `noncomputable` 声明 |
| 已实现 | `Execution/Discrete/EffectiveKernelBehavioralProfile.lean`；`Simulation/Presentation/Kernel/EffectiveBehavioralProfile.lean`；`Simulation/Restart/Observed.lean` | S130 effective high-level adapter、raw policy、任意 finite event/state-prefix、S092--S094 continuation/fresh restart 与 S134 normalized continuation 的逐 horizon 等式；只在显式表示子域与 discrete complete-history model 上成立 |
| 已实现 | `Math/Probability/Effective/{Enclosure,Core,Uniform}.lean`；`Effective/{Semantics,UniformSemantics}.lean`；`Simulation/Equilibrium/EffectivePathUtility.lean` | A19 选定事件／simple-observable 语言的 enclosure、law/map/kernel bind/composition、精确非原子 uniform backend，以及 S082/S085/S086/S101 representation bridges；任意可测集、任意可积函数和零测 RCD 仍是分析边界 |
| 研究扩展 | 有效路径 `L¹` approximation certificate | uniform 版本已实现；若消费者只能给几乎处处或 `L¹` 误差，应另建不要求逐路径界的证书接口 |

新的连续 kernel backend 应在 A19 的封闭事件／观测语言上实现自己的 pullback 和误差
传播，不能以任意 `Measure` 为运行接口。

任何新增算法都至少应给出：终止性、soundness、需要时的 completeness、复杂度或
支持增长说明，以及与现有分析语义的精确等式、误差界或准确范围的几乎处处定理。
