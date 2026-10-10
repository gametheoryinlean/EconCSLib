# 整个 EFG 文件规划：逐文件清单

> Historical development ledger. Counts and checkpoints below describe their
> dated development snapshots. The completed publication subset excludes
> sequential-equilibrium and arbitrary-measure pure-strategy prototypes and
> their adapters. Use `efg-module-status.md` and the live audit tools for the
> submitted module and declaration census.

日期：2026-09-04。本文是[整体规划](efg-file-plan.md)的源文件快照与迁移清单。
阶段 P0–P5 和全部 45 个已建主库实现／语义落点见整体规划；A19 另有纯运行与
分析解释两个导航聚合模块。此处只链接已经存在的文件。
生命周期与当前职责以[权威登记](efg-module-status.md)和现有源码模块文档为准，
本清单不构成新的状态决定；
“规划动作”除明确标注“已建”的阶段外均为将来工作，不表示已经迁移。所有现有文件均有一行。
登记原文中仍有 PMF 等历史术语；具体计算契约以 Lean 中的类型为准，
例如 `FiniteLaw` 存储有限有理原子表。相关表述在对应文件实施时同步修订。

## 1. EFG 主目录：182 个现有 Lean 文件（其中 `Simulation/` 42 个）

文件标签相对 `EconCSLib/GameTheory/ExtensiveGame/`。

| 文件 | 当前角色 | 当前职责（登记／源码） | 规划动作 |
|---|---|---|---|
| [BackwardInduction.lean](../../EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean) | 前端 | Computable structural backward-induction values | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Basic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Basic.lean) | 内部 | State-payoff `ExtensiveGame` compatibility carrier over `Structural.Basic` | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Compiler/FiniteImperfectObserved.lean](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/FiniteImperfectObserved.lean) | 前端 | Compact imperfect-information to observed/chance EFG compilation | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [Compiler/GameTreeObserved.lean](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/GameTreeObserved.lean) | 历史 | Endpoint-observed compiler preserving old endpoint policies | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [Compiler/GameTreeOccurrenceObserved.lean](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/GameTreeOccurrenceObserved.lean) | 前端 | Canonical root-bound occurrence-sensitive tree compiler and pure standard SPE | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [Compiler/StochasticGameTreeObserved.lean](../../EconCSLib/GameTheory/ExtensiveGame/Compiler/StochasticGameTreeObserved.lean) | 前端 | Stochastic-tree to occurrence-sensitive observed-chance compilation | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [Execution/CompletePlay.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/CompletePlay.lean) | 规范层 | Measure-free history-rooted legal complete plays and terminal absorption | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/Discrete/KernelArena.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/KernelArena.lean) | 内部 | Discrete stochastic arena and policy kernel | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/Discrete/KernelTrajectory.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/KernelTrajectory.lean) | 内部 | Discrete policy execution, traces, and coupling transfer | P2：状态策略作为完整历史策略特例；复用或证明有限迭代器对应 |
| [Execution/Discrete/HistoryKernel.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/HistoryKernel.lean) | 内部 | Computable state-history and action-recording finite execution | P2（已建）：保留为有限执行门面的内部实现；后续只添加分析语义对应与实际主库消费者 |
| [Execution/Discrete/FiniteObservation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/FiniteObservation.lean) | 内部 | Exact finite coordinate, tail, fresh-clock restart, and absolute prefix-splicing observations | P2/P4（已建）：保留绝对时钟续局和时间零重启的区别，事件执行后才投影状态 |
| [Execution/Discrete/ConditionalContinuation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/ConditionalContinuation.lean) | 内部 | Exact positive-fiber conditioning and continuation on complete Arena histories and state/event prefixes, with explicit zero-mass failure | P1/P3（已建）：正概率 Bayes 续局、联合律及三种历史载体已进入有限执行门面；分析条件分布仍单独处理 |
| [Execution/Discrete/CertifiedPathApproximation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/CertifiedPathApproximation.lean) | 内部 | Exact rational centers, declared approximation radii, scheme intervals, and least-horizon searches over coherent state/event prefix laws | P3（已建）：预算搜索最多比较 `budget` 个 radius，只计算选中时界的 center；center 对原子表线性。scheme interval 本身不是目标积分误差界，需另有语义证书 |
| [Execution/Discrete/ContinuationTruncation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/ContinuationTruncation.lean) | 内部 | Exact continuation stopped centers, unfinished masses, error radii, and horizon searches from absolute state/event prefixes | P3（已建）：保留绝对时钟与动作历史；预算搜索可重复执行有限前缀，每个前缀律可指数增长；原续局积分误差仍需分析证书 |
| [Execution/Discrete/DiscountedPathUtility.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/DiscountedPathUtility.lean) | 内部 | Exact finite discounted state/event path observables, geometric tail schedules, and radius-qualified horizon search over coherent effective laws | P3（已建）：在非负有理 `γ < 1` 和显式逐期统一界 `B` 下，读取绝对时刻 `start + k` 的 reward，并以从所给起点归一的 `γ^k`（`0 ≤ k < H`）计算前 `H` 项 center 及 `B * γ^H / (1 - γ)` radius；证明 radius 趋零，并复用 A15 搜索与 state→event 投影。已给前缀律的 center 代价对 `H × 原子发生数` 线性，前缀律可指数增长；几何 radius 本身不是无限折扣路径积分证书 |
| [Execution/Discrete/EffectiveKernelBehavioralProfile.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/EffectiveKernelBehavioralProfile.lean) | 内部 | Effective kernel presentation and behavioral profile assembly with finite abstract/realization laws, fixed chance laws, terminal decisions, and coherent prefix execution | P2/P4（已建）：作为离散模型的运行主体，保留两阶段信息动作实现、机会兼容和完整事件前缀；`bind` 支持可相乘，多步执行可指数增长 |
| [Execution/Discrete/EffectivePathLaw.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/EffectivePathLaw.lean) | 内部 | Exact step-indexed state/event prefix laws, coordinate laws, and Boolean cylinder masses computed by the existing finite executor | P2（已建）：较长前缀截断后与较短前缀按 `FiniteLaw.Equivalent` 一致，坐标与柱质量查询保持；保留绝对时钟；不构造无限路径、`Measure` 或任意集合查询，原子表可指数增长 |
| [Execution/Discrete/EffectivePathUtility.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/EffectivePathUtility.lean) | 内部 | Exact rational prefix expectations and horizon-invariance for cylinder observables on coherent state/event path-law queries | P2/P3（已建）：对已给原子表线性计算期望，并证明柱可观测量的时界不变性与状态投影；前缀律生成仍可指数增长，不代称无限路径积分 |
| [Execution/Discrete/FiniteCompleteEventPath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/FiniteCompleteEventPath.lean) | 内部 | Finite laws of on-demand terminal-absorbing complete event paths from bounded execution and positive-support termination certificates | P3（已建）：在终点后吸收回放并保留绝对坐标与动作发生；映射已给原子表为线性，有界执行可指数增长；函数值有限律不是一般无限路径测度 |
| [Execution/Discrete/ObservedChance.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/ObservedChance.lean) | 内部 | Direct bounded event-prefix execution from the original player behavioral and chance `FiniteLaw`s with explicit terminal detection | P2（已建）：玩家／机会局部律、动作事件和绝对时钟均保留，终点返回 `none`；运行接口不接收测度或 presentation，一般非原子机会语义仍留在分析轨 |
| [Execution/Discrete/RealizedInformation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Discrete/RealizedInformation.lean) | 内部 | Measure-free abstract-action selection and dependent concrete realization compiled by `FiniteLaw.bind` and `map` | P2（已建）：依赖返回类型保证当前状态动作合法，optional law 保持终点 killed 分支；不从有限输出推导输入可测性，一般 realization kernel 仍保留 |
| [Execution/FiniteCompletePath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/FiniteCompletePath.lean) | 内部 | On-demand terminal-absorbing complete paths from bounded exact history laws and explicit positive-support termination certificates | P3（已建）：有限历史回放、全坐标边缘一致和正权重合法性均已进入主库；示例保持原位 |
| [Execution/FinitePayoff.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/FinitePayoff.lean) | 内部 | Exact rational finite-horizon expectations and stopped payoffs on complete histories and state/event prefixes | P1（已建）：作为有限执行门面的纯计算收益层；保持完整历史、动作记录、终止判断和未完成质量的零收益约定 |
| [Execution/History.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/History.lean) | 内部 | `ExtensiveGame.unfold` payoff-aware adapter over structural histories | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/InfiniteTrajectory.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/InfiniteTrajectory.lean) | 规范层 | Executable `FiniteLaw` path marginals, exact bounded observables, partial terminal search, and projections of supplied infinite/terminal laws | P1/P3：复用下沉的有限辅助定义，保留所给完整律接口及其证书要求 |
| [Execution/Length.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Length.lean) | 规范层 | Uniform length and `Acc`-based structural well-foundedness certificates | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/Objective.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Objective.lean) | 规范层 | History-sensitive terminal and complete-path outcomes | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/Reachability.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Reachability.lean) | 内部 | `ExtensiveGame.IsReachable` payoff-aware adapter over structural reachability | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/StochasticExecution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/StochasticExecution.lean) | 规范层 | Terminal-aware bounded PMF execution | P1：保留有限历史执行所有权；接收有限未终止质量辅助定义 |
| [Execution/StoppedExecution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/StoppedExecution.lean) | 规范层 | Terminal-aware deterministic bounded execution | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Execution/Truncation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Execution/Truncation.lean) | 内部 | Exact stopped-payoff centers, unfinished-mass radii, budgeted search, and proof-guarded least-horizon search | P3（已建）：纯数值截断内核已进入有限执行门面；几乎必终止到误差存在性的分析证明仍留给语义层 |
| [FOSG/FOSG.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/FOSG.lean) | 前端 | Compact simultaneous stochastic game and weak-serialization contract | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/FOSGBehavioralSerialization.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/FOSGBehavioralSerialization.lean) | 前端 | Reusable strategic bridge for weak serializers | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/FOSGContinuation.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/FOSGContinuation.lean) | 前端 | Macro-root continuation and Nash transfer | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/Sequentialization/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/Core.lean) | 内部 | Serialized micro-state/game construction | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/Sequentialization/Equilibrium.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/Equilibrium.lean) | 内部 | Finite-horizon Nash transfer from the witness | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/Sequentialization/MacroLaw.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/MacroLaw.lean) | 内部 | Exact one-macro-step law | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/Sequentialization/Policy.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/Policy.lean) | 内部 | Source and target policy compilation | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/Sequentialization/Trajectory.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/Trajectory.lean) | 内部 | Iterated micro/macro trace law | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FOSG/Sequentialization/Witness.lean](../../EconCSLib/GameTheory/ExtensiveGame/FOSG/Sequentialization/Witness.lean) | 内部 | Weak-serialization certificate assembly | P4：迁移实际执行／收益消费者，保持该表示已证明的严格或弱保持关系 |
| [FiniteArenaExtraction.lean](../../EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean) | 前端 | Assumption-explicit Arena-to-tree extraction relation | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTree.lean](../../EconCSLib/GameTheory/ExtensiveGame/GameTree.lean) | 前端 | Finite no-chance inductive tree syntax | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTreeNE.lean](../../EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean) | 历史 | Root Nash and endpoint-policy restriction theorems | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [GameTreeSPE.lean](../../EconCSLib/GameTheory/ExtensiveGame/GameTreeSPE.lean) | 历史 | Global structural endpoint-policy optimality | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [GameTreeStrategicForm.lean](../../EconCSLib/GameTheory/ExtensiveGame/GameTreeStrategicForm.lean) | 历史 | Endpoint-plan strategic-form extraction | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [ImperfectInformation.lean](../../EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean) | 前端 | Compact finite-state information-labeled syntax | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Interface/Compilation/Discrete.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Compilation/Discrete.lean) | 规范层 | Governed pre-stability finite compiler and FOSG serialization facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Core.lean) | 规范层 | Governed pre-stability Foundation Facade for typed histories, finite/subgame/recall certificates, and bounded deterministic/PMF execution | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Equilibrium/Analytic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Equilibrium/Analytic.lean) | 规范层 | Governed pre-stability measurable outcome and continuation-equilibrium facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Equilibrium/Discrete.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Equilibrium/Discrete.lean) | 规范层 | Governed pre-stability pure/behavioral/mixed/general finite equilibrium facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Execution/Analytic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Execution/Analytic.lean) | 规范层 | Governed pre-stability non-atomic measurable-kernel execution facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Execution/Finite.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Execution/Finite.lean) | 规范层 | Governed pre-stability measure-free deterministic/PMF execution facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Execution/Infinite.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Execution/Infinite.lean) | 规范层 | Governed pre-stability measure-valued discrete-path facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Objective.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Objective.lean) | 规范层 | Governed pre-stability measure-free outcome, winning-condition, and quasistrategy facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Preservation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Preservation.lean) | 规范层 | Governed pre-stability facade for strict/refinement/weak relation strengths, bounded/path-law realizations, couplings, and compiler preservation packages | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Relations/Discrete.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Relations/Discrete.lean) | 规范层 | Governed pre-stability structural/PMF relation facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Restart.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Restart.lean) | 规范层 | Governed pre-stability fresh-restart compatibility facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/StructuralCore.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/StructuralCore.lean) | 规范层 | Exact five-module structural facade for Arena, reachability, typed histories, complete plays, and payoff-free observed control | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Winning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Winning.lean) | 规范层 | Governed pre-stability logical winning-strategy and determinacy facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Interface/Winning/Stochastic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Interface/Winning/Stochastic.lean) | 规范层 | Governed pre-stability discrete infinite almost-sure-winning facade | P5：保持本入口职责；涉及新增导出时同步政策、生命周期与闭包回归 |
| [Observed/Behavior.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Behavior.lean) | 规范层 | Information-indexed behavioral profiles and history policies | P4：复用同一有限概率和历史执行，保持各自策略分布空间 |
| [Observed/BehaviorMorphism.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/BehaviorMorphism.lean) | 规范层 | Strict behavioral transport and Nash equivalence | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/BehaviorRefinement/Execution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/BehaviorRefinement/Execution.lean) | 规范层 | Behavioral execution and directional Nash transfer | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/BehaviorRefinement/Structural.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/BehaviorRefinement/Structural.lean) | 规范层 | Chance-aware refinement and strategy lifting | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Chance.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Chance.lean) | 规范层 | Normalized chance kernels and chance isomorphisms | P4：复用同一有限概率和历史执行，保持各自策略分布空间 |
| [Observed/Continuation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Continuation.lean) | 规范层 | Pure/behavioral compilation to continuation forms | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/Controlled.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled.lean) | 规范层 | Observation-free decision core, optional private/public observation extension, represented strategy coordinates, bijective player relabeling, pure-profile reindexing, and external root presentations | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Compat/DiscreteLaw.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Compat/DiscreteLaw.lean) | 内部 | Forget-payoff adapter from `ObservedChanceGame` to discrete controlled chance | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Compat/Infrastructure.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Compat/Infrastructure.lean) | 内部 | `ObservedGame` projection and legacy recall/quasistrategy compatibility lemmas | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Compat/Morphism.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Compat/Morphism.lean) | 内部 | Payoff-aware strict-isomorphism commuting square and legacy-Iso projection | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Controlled/Infrastructure.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure.lean) | 规范层 | Declaration-free aggregate facade for controlled execution, well-formedness, subgame, finite, quasistrategy, recall, and winning infrastructure | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Infrastructure/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure/Core.lean) | 规范层 | Reachable no-chance mover helpers, pure-profile history execution, and player-strategy play compatibility | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Infrastructure/Finite.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure/Finite.lean) | 规范层 | Uniform history-length, finite reachable-action/represented-information, and finite-EFG certificate package | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Infrastructure/Quasi.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure/Quasi.lean) | 规范层 | Objective-free quasistrategy permissions, refinement, and play compatibility | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Infrastructure/Recall.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure/Recall.lean) | 规范层 | Personal decisions, own-decision histories, classic recall, event-clock signal/public recall, optional silent-event trace builders, no-absent-mindedness, and recall certificates | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Infrastructure/Subgame.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure/Subgame.lean) | 规范层 | Occurrence-sensitive continuations, lawful/complete subgame systems, and bijective player-relabel transport | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Infrastructure/WellFormed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Infrastructure/WellFormed.lean) | 规范层 | Optional full raw-information representation and mover-normalization predicates plus reachable-execution compatibility bundles | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Controlled/Law.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law.lean) | 规范层 | Per-root lawful complete-path marginals, measurable interpretations, honest history-transform/terminal-history laws, execution-coherence certificates, realizations, and strict-Iso bridges | 保留共同路径律载体；不将有限、非原子与所给无限律合并成单一 executor |
| [Observed/Controlled/Law/Analytic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law/Analytic.lean) | 规范层 | Measurable-kernel adapter to the common lawful complete-path probability carrier | P2/P4：保持一般分析适配，消费新的有限语义等式 |
| [Observed/Controlled/Law/Discrete.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law/Discrete.lean) | 规范层 | Payoff-free discrete chance kernels, raw `BoundedHistoryLawFamily`, and normalized/legal/absorbing/executor-consistent `CertifiedBehavioralExecutionLaw` | P2/P4：接入通用有限 executor，继续由执行构造合法／吸收／概率证书 |
| [Observed/Controlled/Law/DiscretePath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Law/DiscretePath.lean) | 规范层 | Supplied discrete behavioral complete-path laws with exact executable `FiniteLaw` marginal and legality certificates | P3：接入有界终止完整路径构造；保留一般输入契约 |
| [Observed/Controlled/Morphism.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Morphism.lean) | 规范层 | Declaration-free aggregate facade for payoff-free structural, lawful-subgame, recall, and objective-semantics morphism leaves | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Controlled/Morphism/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Morphism/Core.lean) | 规范层 | Payoff-free Hom, information refinement, strict Iso, carrier/history/action/strategy maps, root-presentation comparison, inverse, and Iso algebra | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Controlled/Morphism/Objective.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Morphism/Objective.lean) | 规范层 | Pure execution and terminal-objective transport under strict Iso and directional information refinement, each with an explicit objective-compatibility square | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Controlled/Morphism/Recall.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Morphism/Recall.lean) | 规范层 | Strict-Iso preservation of personal decisions, own-decision histories, event-clock signal histories, and classic/event-clock private/public recall | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Controlled/Morphism/Subgame.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Morphism/Subgame.lean) | 规范层 | Strict-Iso preservation of occurrence-sensitive continuation, lawful roots, and selected/complete subgame systems | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Controlled/Semantics.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Controlled/Semantics.lean) | 规范层 | Concrete pure terminal/path-objective continuation and SPE plus payoff-free evaluator-relative continuation transfer | P4：接入收益计算，保持 evaluator-relative 与实际纯执行的区别 |
| [Observed/DeferredSampling/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/DeferredSampling/Core.lean) | 内部 | Fresh information keys and finite table laws | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/DeferredSampling/Execution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/DeferredSampling/Execution.lean) | 内部 | Fresh-query execution equivalence | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/DeferredSampling/Realization.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/DeferredSampling/Realization.lean) | 内部 | Deferred behavioral/mixed continuation transfer | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/FiniteUnfolding.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/FiniteUnfolding.lean) | 规范层 | Finite occurrence-sensitive reachable-history extraction with strict structural, root/subgame, recall, chance, strategy/update, and bounded-history-law preservation | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/FinitePureNash.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/FinitePureNash.lean) | 内部 | Executable finite-horizon Nash checking over the original root-bound pure strategy and unilateral-deviation spaces | P4（已建）：`all` 在 `Fintype` 上无重复枚举通过检查的 profile，有序 `find` 显式要求 `FinEnum`；每次检查枚举全部单方偏离，全搜索再乘以 profile 数；不代称最终效用或一般纯 Nash 存在性 |
| [Observed/Game.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Game.lean) | 规范层 | State-payoff observed-game information, two-way payoff attachment/erasure, bijective player/payoff reindexing, external root presentations, and compatibility names for controlled lawful systems | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/General.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/General.lean) | 规范层 | Countably supported general strategies over behavioral plans | P4：复用同一有限概率和历史执行，保持各自策略分布空间 |
| [Observed/InfiniteExecution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/InfiniteExecution.lean) | 规范层 | Observed behavioral indexing and finite-marginal certificates for supplied infinite execution | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Kuhn.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Kuhn.lean) | 规范层 | Finite hypotheses and behavioral-to-mixed realization | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/KuhnConditioning/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/KuhnConditioning/Core.lean) | 内部 | Posterior products and recall identities | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/KuhnConditioning/Execution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/KuhnConditioning/Execution.lean) | 内部 | Sequential posterior execution equality | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/KuhnConditioning/Posterior.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/KuhnConditioning/Posterior.lean) | 内部 | Posterior conditioning of complete plans | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/KuhnConditioning/Realization.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/KuhnConditioning/Realization.lean) | 内部 | Root-scoped mixed-to-behavioral law transfer | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/LawEquivalence.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/LawEquivalence.lean) | 规范层 | Bounded complete-history-law realizations and terminal/payoff pushforwards | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Mixed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Mixed.lean) | 规范层 | Mixed complete plans and bounded mixed execution | P4：复用同一有限概率和历史执行，保持各自策略分布空间 |
| [Observed/Morphism/Continuation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Morphism/Continuation.lean) | 规范层 | Total continuation and lawful-system transport | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Morphism/Inverse.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Morphism/Inverse.lean) | 内部 | Inverse structural transport proofs | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Morphism/Operational.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Morphism/Operational.lean) | 规范层 | Exact finite execution transport | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Morphism/Structural.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Morphism/Structural.lean) | 规范层 | Strict observed-EFG isomorphism structure | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/MorphismHierarchy.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/MorphismHierarchy.lean) | 规范层 | Relation hierarchy and agreement regressions | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/PerfectRecall.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/PerfectRecall.lean) | 内部 | Legacy `ObservedGame` classic-recall names and strict-Iso adapters projected from payoff-free theory | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Quasi.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Quasi.lean) | 内部 | Legacy `ObservedGame` quasistrategy names projected from the payoff-free implementation | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Realization.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Realization.lean) | 规范层 | Law-valued behavioral realization adapters | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/Refinement/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Refinement/Core.lean) | 规范层 | Pure bounded execution and directional Nash transfer | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Refinement/Structural.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Refinement/Structural.lean) | 规范层 | Information-refinement structure and maps | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/Refinement/Termination.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Refinement/Termination.lean) | 规范层 | Termination-certified refinement transfer | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Observed/SPE.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/SPE.lean) | 规范层 | Total pure execution, lawful-root and standard SPE | P4：保持完整合法子博弈系统和原偏离空间；复用有限收益 |
| [Observed/SemanticMode.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/SemanticMode.lean) | 规范层 | Lightweight strategy/chance semantic classification tags | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/Semantics.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/Semantics.lean) | 规范层 | State-payoff `ObservedGame` adapter for controlled evaluator-relative continuation semantics | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/SignalRecall.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/SignalRecall.lean) | 内部 | Payoff-aware `ObservedGame` projections of event-clock signal/public recall and recall certificates | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Observed/StrategyBridge.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/StrategyBridge.lean) | 规范层 | Uniform public navigation across strategy modes | P4：复用通用概率与条件化；保持回忆、有限性及选定根假设 |
| [Observed/WellFormed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Observed/WellFormed.lean) | 规范层 | Full information representation, decision coherence, and structural finite-EFG certificates | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Relations/Discrete/KernelWeakSimulation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Relations/Discrete/KernelWeakSimulation.lean) | 内部 | Positive-fuel weak/stuttering kernel simulation | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Relations/Discrete/Morphism.lean](../../EconCSLib/GameTheory/ExtensiveGame/Relations/Discrete/Morphism.lean) | 内部 | Arena homomorphism, simulation, bisimulation, and weak simulation | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Relations/Discrete/StochasticNaturality.lean](../../EconCSLib/GameTheory/ExtensiveGame/Relations/Discrete/StochasticNaturality.lean) | 规范层 | Exact PMF history-execution naturality under strict arena isomorphisms | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Relations/Preservation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Relations/Preservation.lean) | 规范层 | Formal preservation-matrix certificate aliases, coupling interfaces, and compiler-specific strict/weak packages | P4：迁移证明消费者，保留同构／细化／耦合／弱模拟强度 |
| [Simulation/Continuation/Conditioning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Conditioning.lean) | 内部 | Raw positive-prefix conditional-law bridge and finite effective tail marginals of continuation/RCD kernels | P3/P4（已建有限 tail 桥）：有效 raw event policy 的任意有限 `tailPrefixLawFrom` Dirac 边缘等于 represented prefix 上原 `continuationTailKernel` 的 `frestrictLe`；对 singleton prefix 质量非零且满足 Standard Borel/单点可测条件时，还等于 RCD `conditionalTailKernel` 的相同边缘。保留完整前缀与绝对时钟；零质量 prefix 版本选择和整体无限核等式未声称 |
| [Simulation/Continuation/FiniteConditioning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/FiniteConditioning.lean) | 内部 | Exact finite-posterior continuation correspondence with analytic partial trajectories and absolute-path marginals | P3（已建）：有限 posterior 先重索引到可测前缀空间；零质量观测仍返回 `none`，不选择零测条件核版本 |
| [Simulation/Continuation/Observed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Observed.lean) | 内部 | Absolute/fresh continuation outcomes and equilibrium | P3/P4：复用有限条件续局／收益对应；保留原历史、根和零测边界 |
| [Simulation/Continuation/ObservedConditioning.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/ObservedConditioning.lean) | 内部 | Supplied positive-prefix conditional laws and expectations | P3/P4：复用有限条件续局／收益对应；保留原历史、根和零测边界 |
| [Simulation/Continuation/Path.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Continuation/Path.lean) | 内部 | Absolute-prefix analytic continuation paths | P3/P4：复用有限条件续局／收益对应；保留原历史、根和零测边界 |
| [Simulation/Equilibrium/FinitePayoff.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/FinitePayoff.lean) | 内部 | Exact rational finite-payoff integral semantics, unfinished-mass identity, and truncation-radius bound for Arena histories and KernelArena state/event prefixes | P3（已建）：计算定义仍返回有理数；积分只作为语义定理；所给路径律需有限边缘一致证书；目标收益前提显式保留 |
| [Simulation/Equilibrium/EffectivePathUtility.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/EffectivePathUtility.lean) | 内部 | Effective simple-observable expectation certificate for analytic path utility | P4（已建）：有效 law 表示原 state-path Measure，且调用者提供有限有理 simple observable 的 `Denotes` 证书时，expectation oracle 表示原 `expectedUtility`；任意可积函数不会自动产生该证书 |
| [Simulation/Equilibrium/Outcome.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Equilibrium/Outcome.lean) | 内部 | Path utilities, Nash, termination, and payoff convergence | P3/P4：复用有限收益与截断桥接；保留全定义路径效用与原均衡结论 |
| [Simulation/Kernel/Arena.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Arena.lean) | 内部 | Non-atomic analytic arena and discrete embedding | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/CertifiedPathApproximation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/CertifiedPathApproximation.lean) | 内部 | Analytic finite-marginal and uniform-error certificates for effective state-prefix approximation | P3（已建）：在分析无限状态路径律的每个所需有限边缘等于有效 prefix law，且外部实值效用可测可积、lifted observable 可测并满足真实逐点统一 radius 界时，证明有理 center 等于 prefix integral、scheme interval 包含目标积分，成功搜索的真实误差不超过 tolerance。所有分析对象均为 theorem-only 证据；不把目标积分传给算法、不自动认证任意 scheme，也不构造无限 `Measure` |
| [Simulation/Kernel/DiscreteBridge.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/DiscreteBridge.lean) | 内部 | Exact discrete-path/analytic-path coherence | P2：新有限语义叶复用既有全路径一致性证明 |
| [Simulation/Kernel/Endpoint.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Endpoint.lean) | 内部 | Supplied analytic endpoint kernels with exact iteration certificates | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/EventPath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EventPath.lean) | 内部 | Joint state/action event-path execution | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/EffectivePathLaw.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/EffectivePathLaw.lean) | 内部 | Weighted-Dirac semantics of every horizon in coherent executable prefix laws and reindexed event/state tails | P2（已建）：任意给定前缀及根的有限律精确等于原 `partialTraj`；每个有限重编号 event tail 及其 state projection 等于原 `tailEventPathMeasureFromPrefix`/`tailStatePathMeasureFromPrefix` 的 `frestrictLe` 边缘。只复用局部策略实现条件，不构造整体无限测度或任意可测事件算法 |
| [Simulation/Kernel/Execution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/Execution.lean) | 内部 | Legal terminal-aware analytic one-step policy | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/FiniteCompleteEventPath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/FiniteCompleteEventPath.lean) | 内部 | Analytic prefix and coordinate semantics for bounded terminal-absorbing complete event-path laws | P3（已建）：有限 weighted-Dirac 解释的所有前缀和坐标边缘等于原 `partialTraj`，超过终止 bound 仍成立；逐时界有限边缘正确不等于已构造整体无限路径 `Measure` |
| [Simulation/Kernel/FiniteExecution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/FiniteExecution.lean) | 内部 | Exact one-step and arbitrary finite-prefix finite-law/analytic-kernel correspondence | P2（已建）：保留局部可测实现条件；任意初始前缀、绝对时钟、状态和动作事件多步等式已证明 |
| [Simulation/Kernel/FiniteRealizedInformation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/FiniteRealizedInformation.lean) | 内部 | Analytic bridge from finite abstract-law/realization `bind` compilation to the existing realized information kernel | P2（已建）：在两项局部表示条件下证明 realized kernel 与 bundle 律逐点相等，并覆盖终点 killed 质量；不从任意有限律值函数制造可测核 |
| [Simulation/Kernel/HistoryPath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/HistoryPath.lean) | 内部 | Prefix-dependent state-history policy execution | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/ObservedEvent.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/ObservedEvent.lean) | 内部 | Fixed information-indexed event policies | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/RealizedInformation.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/RealizedInformation.lean) | 内部 | Abstract action realization for observed event policies | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Kernel/StatePath.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Kernel/StatePath.lean) | 内部 | Supplied infinite state law and exact prefix/coordinate marginals | P2/P3：保留一般分析定义；有限前缀、事件及完整路径特例由通用等式连接 |
| [Simulation/Presentation/Chance/Countable.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Countable.lean) | 内部 | Effective countable information/action selectors; supplied analytic boundary | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Chance/FiniteExecution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/FiniteExecution.lean) | 内部 | Exact local, event-prefix, and complete state-prefix correspondence between direct observed-chance execution and compiled measurable presentations | P2/P4（已建）：终点／非终点 action law 及任意时界 weighted-Dirac event-prefix 律等于原 analytic policy／`partialTraj`；先完整执行事件前缀再 map states，得到原 `statePathMeasure` 的任意有限 `frestrictLe` 边缘。执行器不求值 realization kernel，一般可测及非原子 presentation 保留 |
| [Simulation/Presentation/Chance/KernelBridge.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/KernelBridge.lean) | 内部 | Complete-history observed PMF-to-kernel bridge | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Chance/Measurable.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Measurable.lean) | 内部 | Explicit uncountable observed-chance presentation | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Chance/MeasurableHistory.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/MeasurableHistory.lean) | 内部 | Explicit measurable complete-history model | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Chance/ProfileAssembly.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/ProfileAssembly.lean) | 内部 | Compatibility seam from PMF profiles to measurable assembly | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Chance/Realized.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Chance/Realized.lean) | 内部 | Explicit observed-chance realization certificate | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Kernel/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/Core.lean) | 内部 | Non-atomic observed kernel-valued strategy presentation | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Presentation/Kernel/EffectiveBehavioralProfile.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/EffectiveBehavioralProfile.lean) | 内部 | Weighted-Dirac realization of effective kernel profiles, compiled-policy equality, and exact event/state finite-prefix analytic marginals | P2/P4（已建）：在显式可测等价与局部 Dirac 表示证书下精确连接原 `KernelBehavioralProfile`；事件前缀等于 `partialTraj`，完整执行后的 state projection 等于原高层 `statePathMeasure` 的任意有限 `frestrictLe` 边缘。这是离散模型桥，不从逐点有限性推出可测性或无限路径测度 |
| [Simulation/Presentation/Kernel/ProfileAssembly.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Presentation/Kernel/ProfileAssembly.lean) | 内部 | Measurable player profiles with executable role decisions and deviations | P2/P4：有限有效 profile 复用通用计算；任意可测表示与合法性条件保留 |
| [Simulation/Restart/Assembly.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Assembly.lean) | 内部 | Baseline-and-deviation compatibility assembly | P4：有限拼接复用通用执行；验证绝对时钟、信息重基与实际偏离传输 |
| [Simulation/Restart/Certificates.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Certificates.lean) | 内部 | Raw step/action/path restart certificates | P4：有限拼接复用通用执行；验证绝对时钟、信息重基与实际偏离传输 |
| [Simulation/Restart/Core.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Core.lean) | 内部 | Root-event normalization and finite splicing | P4：有限拼接复用通用执行；验证绝对时钟、信息重基与实际偏离传输 |
| [Simulation/Restart/Equilibrium.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Equilibrium.lean) | 内部 | Canonical restart/continuation equilibrium transfer | P4：有限拼接复用通用执行；验证绝对时钟、信息重基与实际偏离传输 |
| [Simulation/Restart/Factorization.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Factorization.lean) | 内部 | Statistic and information-rebase certificate constructors | P4：有限拼接复用通用执行；验证绝对时钟、信息重基与实际偏离传输 |
| [Simulation/Restart/FiniteExecution.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/FiniteExecution.lean) | 内部 | Exact finite-law correspondence for fresh-clock, absolute-clock, and spliced restart prefixes at every horizon | P4（已建）：纯执行器的三类有限前缀律已直接等同于原 restart 分析测度；两种时钟保持分离 |
| [Simulation/Restart/Observed.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Observed.lean) | 内部 | Observed-profile lift and A20 finite effective marginals for absolute-clock continuation, normalized tails, and fresh restart | P4（已建有限桥）：在 discrete complete-history representation 下，A20 每个 horizon 的 absolute-clock event tail、执行后 state projection、time-zero fresh-restart state 及仅规范化 tail 坐标零 incoming-action marker 的前缀，分别等于原 `continuationEventPathMeasure`、`continuationStatePathMeasure`、`freshRestartStatePathMeasure` 和 `normalizedContinuationEventPathMeasure` 的 `frestrictLe` 边缘。fresh restart 不与绝对时钟续局混同；不声称整体无限 `Measure` 可执行或零质量 RCD 等式 |
| [Simulation/Restart/Trajectory.lean](../../EconCSLib/GameTheory/ExtensiveGame/Simulation/Restart/Trajectory.lean) | 内部 | Spliced trajectory and finite-prefix laws | P4：有限拼接复用通用执行；验证绝对时钟、信息重基与实际偏离传输 |
| [StochasticGameTree.lean](../../EconCSLib/GameTheory/ExtensiveGame/StochasticGameTree.lean) | 前端 | Finite stochastic occurrence-sensitive tree syntax | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Strategy.lean](../../EconCSLib/GameTheory/ExtensiveGame/Strategy.lean) | 历史 | State-indexed Arena strategies without observed information | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [Structural/Basic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Structural/Basic.lean) | 规范层 | Minimal payoff-free `Arena` and `ControlledGame` carriers | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Structural/History.lean](../../EconCSLib/GameTheory/ExtensiveGame/Structural/History.lean) | 规范层 | Typed finite histories and payoff-free Arena/controlled-game unfolding | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Structural/Reachability.lean](../../EconCSLib/GameTheory/ExtensiveGame/Structural/Reachability.lean) | 规范层 | Finite Arena reachability and controlled-game initial reachability | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Subgame.lean](../../EconCSLib/GameTheory/ExtensiveGame/Subgame.lean) | 历史 | State re-rooting and reachable-state restriction | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [Winning/Basic.lean](../../EconCSLib/GameTheory/ExtensiveGame/Winning/Basic.lean) | 规范层 | Complete-play winning conditions, prefix decisions, and robust pure winning strategies | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Winning/BasicCompat.lean](../../EconCSLib/GameTheory/ExtensiveGame/Winning/BasicCompat.lean) | 内部 | Legacy payoff-aware winning-strategy compatibility layer | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Winning/Chance.lean](../../EconCSLib/GameTheory/ExtensiveGame/Winning/Chance.lean) | 规范层 | Almost-sure winning under discrete infinite history laws | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Winning/Determinacy.lean](../../EconCSLib/GameTheory/ExtensiveGame/Winning/Determinacy.lean) | 规范层 | Logical determinacy predicates, imperfect-information boundary, and proved finite and well-founded perfect-information two-player zero-sum determinacy | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Winning/DeterminacyCompat.lean](../../EconCSLib/GameTheory/ExtensiveGame/Winning/DeterminacyCompat.lean) | 内部 | Legacy `ObservedGame` determinacy packages and well-formedness bridges | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Winning/Topology.lean](../../EconCSLib/GameTheory/ExtensiveGame/Winning/Topology.lean) | 规范层 | Complete-play agreement cylinders, prefix topology, and measurable prefix objectives | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Zermelo.lean](../../EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean) | 前端 | Chance-free finite two-player zero-sum tree theorem | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [ZeroSumGameTreeWithChance.lean](../../EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean) | 前端 | Exact rational binary chance-tree value and saddle algorithms | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |

## 2. 直接配套模块：36 个现有 Lean 文件（与 EFG 主目录合计 218 个）

包含表示无关 GameForm、有限／有效概率及剩余旧 PMF 家族。
其他 Foundation／Math／StrategicGame 依赖按实际 imports 复用，不并入 EFG 或复制定义。

| 文件 | 当前角色 | 当前职责（登记／源码） | 规划动作 |
|---|---|---|---|
| [GameTheory/GameForm.lean](../../EconCSLib/GameTheory/GameForm.lean) | 规范层 | Governed aggregate for representation-neutral semantics | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/Basic.lean](../../EconCSLib/GameTheory/GameForm/Basic.lean) | 规范层 | Deterministic game forms, morphisms, and Nash transfer | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/Continuation/Core.lean](../../EconCSLib/GameTheory/GameForm/Continuation/Core.lean) | 规范层 | Continuation forms and functional transfer | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/Continuation/Iso.lean](../../EconCSLib/GameTheory/GameForm/Continuation/Iso.lean) | 规范层 | Invertible continuation semantics | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/Continuation/Simulation.lean](../../EconCSLib/GameTheory/GameForm/Continuation/Simulation.lean) | 规范层 | Relational-root continuation simulation | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/IndexedContinuation.lean](../../EconCSLib/GameTheory/GameForm/IndexedContinuation.lean) | 规范层 | Arbitrary-index continuation adapter | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/Law.lean](../../EconCSLib/GameTheory/GameForm/Law.lean) | 规范层 | Law-valued game forms and exact realization | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [GameTheory/GameForm/LimitSPE.lean](../../EconCSLib/GameTheory/GameForm/LimitSPE.lean) | 历史 | Uniform-limit Nash on caller-declared roots under a legacy path name | 保留历史语义及现有消费者；不建立与发生位置／标准子博弈语义的虚假等价 |
| [Math/Probability/Effective.lean](../../EconCSLib/Math/Probability/Effective.lean) | 规范层 | Measure-free aggregate for executable effective-probability queries | P4（已建）：纯运行导航聚合，不导入 Measure／Kernel／积分；算法 owner 位于其 leaves |
| [Math/Probability/Effective/Analytic.lean](../../EconCSLib/Math/Probability/Effective/Analytic.lean) | 规范层 | Opt-in aggregate for analytic correctness of effective probability queries | P4（已建）：导入纯聚合和两个 semantics leaves；不改变计算值的所有权 |
| [Math/Probability/Effective/Enclosure.lean](../../EconCSLib/Math/Probability/Effective/Enclosure.lean) | 内部 | Exact rational enclosures and arbitrary-positive-tolerance oracles | P4（已建）：区间算术与误差宽度均用精确有理数执行，不依赖 Measure／Kernel／积分 |
| [Math/Probability/Effective/Core.lean](../../EconCSLib/Math/Probability/Effective/Core.lean) | 内部 | Coded-event effective laws, finite rational simple observables, maps, bind, and kernel composition | P4（已建）：事件类型由模型选择；pushforward 需可执行逆像编译器；kernel 以 observable transformer 表示，从而闭合 bind／composition |
| [Math/Probability/Effective/Semantics.lean](../../EconCSLib/Math/Probability/Effective/Semantics.lean) | 内部 | Proof-only analytic representation of effective laws, maps, kernels, and simple observables | P4（已建）：调用者以关系证书解释事件和 observable；证明 oracle enclosure 包含真实概率／积分及 map／bind／composition 正确性，不向算法层添加分析数据 |
| [Math/Probability/Effective/Uniform.lean](../../EconCSLib/Math/Probability/Effective/Uniform.lean) | 内部 | Exact non-atomic unit-interval backend over rational interval-union event codes | P4（已建）：每个选定事件精确返回 singleton rational enclosure；这是具体非原子 backend，不是任意实集合 oracle |
| [Math/Probability/Effective/UniformSemantics.lean](../../EconCSLib/Math/Probability/Effective/UniformSemantics.lean) | 内部 | Volume and constant-kernel semantics for the effective unit-interval backend | P4（已建）：证明事件 oracle 和 simple-observable expectation 表示真实 volume，并证明 constant effective kernel 的分析正确性 |
| [Math/Probability/FiniteLaw.lean](../../EconCSLib/Math/Probability/FiniteLaw.lean) | 规范层 | Governed aggregate for executable exact finite laws | 保留纯计算聚合；Measure 解释叶继续单独导入 |
| [Math/Probability/FiniteLaw/Conditioning.lean](../../EconCSLib/Math/Probability/FiniteLaw/Conditioning.lean) | 内部 | Partial exact conditioning on Boolean events | P1：提取与 EFG 无关的 Bayes 期望和联合条件化定理 |
| [Math/Probability/FiniteLaw/Core.lean](../../EconCSLib/Math/Probability/FiniteLaw/Core.lean) | 内部 | Sparse rational laws, composition, mass, and expectation | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Math/Probability/FiniteLaw/Coupling.lean](../../EconCSLib/Math/Probability/FiniteLaw/Coupling.lean) | 内部 | Constructive relation-supported exact finite-law couplings | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Math/Probability/FiniteLaw/DeferredSampling.lean](../../EconCSLib/Math/Probability/FiniteLaw/DeferredSampling.lean) | 内部 | Constructive fresh-query deferred-sampling theorem | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Math/Probability/FiniteLaw/Measure.lean](../../EconCSLib/Math/Probability/FiniteLaw/Measure.lean) | 内部 | Analytic measure and integral theorems for exact finite laws | P1（已建）：保持独立分析叶；有限算法继续只依赖纯 `FiniteLaw` 聚合 |
| [Math/Probability/FiniteLaw/Product.lean](../../EconCSLib/Math/Probability/FiniteLaw/Product.lean) | 内部 | Ordered finite dependent products | 保留现有路径与职责；仅在实际依赖受影响时迁移消费者 |
| [Math/Probability/FiniteMarkovChain.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain.lean) | 内部 | Exact finite absorbing-chain execution, full-domain absorption checking, and rational Bellman solving with explicit failure | P3（已建）：纯计算层保留瞬态／终态区分、自动全域检查和显式失败；不把任意 EFG 历史压成 Markov 状态 |
| [Math/Probability/FiniteMarkovChain/Semantics.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/Semantics.lean) | 内部 | Analytic correctness of the exact chain checker and solver via the original first-hit law, reward integral, and duration integral | P3（已建）：证明自动检查等价于全域吸收，精确解等于原首达奖励与时间积分；保持为单独分析叶 |
| [Math/Probability/FiniteMarkovChain/Reachability.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/Reachability.lean) | 内部 | Pure exact reachability, per-terminal and nontermination probabilities from finite reachability pruning plus a rational Cramer solve | P3（已建）：任意有限有理链均给出首达／非终止值和可验证 `outcomeLaw?`，独立语义叶证明其精确首达正确性并保留闭合非终止类；不把历史依赖 EFG 压成有限 Markov 状态，也不处理一般无限或实数链 |
| [Math/Probability/FiniteMarkovChain/ReachabilitySemantics.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/ReachabilitySemantics.lean) | 内部 | Nonsingularity, unique Bellman correctness, outcome-law validation, finite-horizon decomposition, and vanishing late-hit mass for the pruned solver | P3（已建）：证明计算概率与原有限链首达语义一致并显式识别非终止质量；保持独立分析叶，不推广为任意 EFG 或任意路径事件算法 |
| [Math/Probability/FiniteMarkovChain/Discounted.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/Discounted.lean) | 内部 | Exact rational discounted Bellman solving, finite unrolling, uniqueness, and geometric remainder bounds without an absorption premise | P3（已建）：检查 `0 ≤ γ < 1`，对瞬态 reward `r : Fin n → ℚ` 用密集 Cramer 法求解 `(I - γQ)v = r`，命中终点后 reward 为零；闭合非终止类可处理，非奇异、唯一性、展开及余项界已证明；当前 Leibniz 行列式／Cramer 的系数运算最坏为阶乘量级，另有有理数位长成本。没有实现终点持续回报、一般实折扣或平均回报 |
| [Math/Probability/FiniteMarkovChain/Automaton.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/Automaton.lean) | 内部 | Exact product with finite deterministic terminal-time monitors, accepted-terminal values, and explicit nontermination mass | P3（已建）：这是终止时有限词 DFA monitor；初始标签只消费一次，接受值的首达概率解释可实例化通用 reachability 语义并保留其 weight-valid／Bellman correctness 前提。乘积链有 `nq` 个瞬态和 `mq` 个终态，密集 Cramer 求解维度为 `nq` 且现有行列式最坏为阶乘量级。不称为 Büchi/parity；无限运行 min-parity 由独立 `Parity.lean` 拥有 |
| [Math/Probability/FiniteMarkovChain/Parity.lean](../../EconCSLib/Math/Probability/FiniteMarkovChain/Parity.lean) | 内部 | Total exact min-parity classification by positive-support reachability, bottom SCCs, and rational Bellman solving on the total finite chain | P3（已建）：原终态作概率一自环，接受条件是底 SCC 最小 priority 为偶数；`solveParity` 对每个规范化有限有理链都给出总的有理解，非奇异、方程、范围及互补均已证明；接受／拒绝向量分别等于两终点归约链的 `terminalProbability 0/1`。单次 least-closed-set reachability Boolean 判定在朴素 `Finset` membership 成本模型下最坏为 `O(2^N N^3)`，不是整个 solver 的复杂度；后续 `N × N` 密集有理 Leibniz 行列式／Cramer 最坏为阶乘量级并另有有理位长增长。当前只有 min-parity API；max-parity、原链进入底 SCC 与底 SCC 内无限常返证明、分析路径测度上的 ω-event 等式尚未实现 |
| [Math/Probability/RationalIntervalUnion.lean](../../EconCSLib/Math/Probability/RationalIntervalUnion.lean) | 内部 | Pure exact inclusion-exclusion evaluator for finite rational interval-union descriptions | P3（已建）：执行层只接受有限有理描述，精确处理相交、重复、裁剪、反向和单点区间；不引入任意实数比较 |
| [Math/Probability/RationalIntervalUnion/Volume.lean](../../EconCSLib/Math/Probability/RationalIntervalUnion/Volume.lean) | 内部 | Set and unit-interval volume semantics of the rational event evaluator, including probability bounds | P3（已建）：独立分析叶证明原非原子体积等式及 `[0,1]` 界；不把非原子测度改成有限律 |
| [Math/Probability/PMF/ConditionalProduct.lean](../../EconCSLib/Math/Probability/PMF/ConditionalProduct.lean) | 内部 | Legacy conditional finite products | P4：审计实际消费者后逐项迁移；删除须保留原语义且确认消费者归零 |
| [Math/Probability/PMF/ConditionalSampling.lean](../../EconCSLib/Math/Probability/PMF/ConditionalSampling.lean) | 内部 | Legacy discrete fiber conditioning | P4：审计实际消费者后逐项迁移；删除须保留原语义且确认消费者归零 |
| [Math/Probability/PMF/Equiv.lean](../../EconCSLib/Math/Probability/PMF/Equiv.lean) | 内部 | Legacy PMF pushforward equivalences | P4：审计实际消费者后逐项迁移；删除须保留原语义且确认消费者归零 |
| [Math/Probability/PMF/FiniteProduct.lean](../../EconCSLib/Math/Probability/PMF/FiniteProduct.lean) | 内部 | Legacy dependent independent products | P4：审计实际消费者后逐项迁移；删除须保留原语义且确认消费者归零 |
| [Math/Probability/PMF/ToMeasure.lean](../../EconCSLib/Math/Probability/PMF/ToMeasure.lean) | 内部 | PMF/Giry bridge for analytic consumers | P4：审计实际消费者后逐项迁移；删除须保留原语义且确认消费者归零 |

## 3. EFG 示例：69 个现有 Lean 文件

文件标签相对 `EconCSLib/Examples/ExtensiveGame/`。提取通用代码后仍保留具体模型与回归。

| 文件 | 规划动作 |
|---|---|
| [AbsentMinded.lean](../../EconCSLib/Examples/ExtensiveGame/AbsentMinded.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [AnalyticEquilibriumImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/AnalyticEquilibriumImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [AnalyticImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/AnalyticImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [ContinuousKernelBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ContinuousKernelBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ControlledApiImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ControlledApiImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [ControlledMorphismCoreImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ControlledMorphismCoreImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [CoreImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/CoreImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [CouplingBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/CouplingBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [DesignatedContinuationSPEBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/DesignatedContinuationSPEBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [DiscreteCompilationImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/DiscreteCompilationImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [DiscreteEquilibriumImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/DiscreteEquilibriumImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [DiscreteRelationsImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/DiscreteRelationsImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [EFGInfrastructureApiBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/EFGInfrastructureApiBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [EventHistoryKernelBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/EventHistoryKernelBoundary.lean) | P2：成为通用历史核 executor 的消费者；保留相同状态不同动作记忆反例 |
| [FiniteCompletePath.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteCompletePath.lean) | P3：提取历史回放和有限完整路径构造；保留零权重、历史前缀回归 |
| [FiniteConditionalContinuation.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteConditionalContinuation.lean) | P1/P3：通用 Bayes 下沉数学层，续局计算与分析证明分层；保留具体观测博弈 |
| [FiniteEFGWellFormedness.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteEFGWellFormedness.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [FiniteExecutionImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteExecutionImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [FiniteExecutionIntegral.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteExecutionIntegral.lean) | P1/P2/P3：算法、路径等式、效用积分分别提取；保留具体博弈 |
| [FiniteImperfectCompilation.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteImperfectCompilation.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [FiniteLawIntegral.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteLawIntegral.lean) | P1：通用定理提取至数学 Measure 解释叶；保留数值与稀疏列表回归 |
| [FiniteMarkovChain.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteMarkovChain.lean) | P3：通用链计算、自动检查和求解器已进入数学层；本文件仅规划保留具体链与失败用例，本阶段不修改示例 |
| [FiniteMarkovChainSemantics.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteMarkovChainSemantics.lean) | P3：通用吸收与首达积分定理已进入数学语义叶；本文件仅规划保留具体验证，本阶段不修改示例 |
| [FinitePureNash.lean](../../EconCSLib/Examples/ExtensiveGame/FinitePureNash.lean) | P4：通用策略表检查进入 Observed；保留协调／无纯 Nash 的具体博弈 |
| [FiniteReachableUnfolding.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteReachableUnfolding.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [FiniteTruncation.lean](../../EconCSLib/Examples/ExtensiveGame/FiniteTruncation.lean) | P3：提取数值内核与分析终止／误差证明；保留几何尾部、预算和时钟回归 |
| [HistoryDependentKernelBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/HistoryDependentKernelBoundary.lean) | P2：成为通用历史核 executor 的消费者；保留同状态不同初始历史反例 |
| [HistoryDiamond.lean](../../EconCSLib/Examples/ExtensiveGame/HistoryDiamond.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [HistoryObjectiveContinuation.lean](../../EconCSLib/Examples/ExtensiveGame/HistoryObjectiveContinuation.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [InfiniteExecutionImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/InfiniteExecutionImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [InfiniteInformationKuhnBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/InfiniteInformationKuhnBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [InfiniteSPEBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/InfiniteSPEBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [MeasurableKernelContinuationNashBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/MeasurableKernelContinuationNashBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [MeasurableKernelFreshRestartClockBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/MeasurableKernelFreshRestartClockBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [MeasurableKernelRestartInformationRebaseBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/MeasurableKernelRestartInformationRebaseBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [NonmeasurableFiberLegalityBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/NonmeasurableFiberLegalityBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObjectiveImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObjectiveImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [ObservedChanceCountablePresentationBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceCountablePresentationBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedChanceCountableSparsePlayersBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceCountableSparsePlayersBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedChanceKernelBridgeBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceKernelBridgeBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedChanceMeasurableUncountableBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceMeasurableUncountableBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedChanceRealizedPresentationBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedChanceRealizedPresentationBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedEventKernelBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedEventKernelBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedKernelProfileAssemblyBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedKernelProfileAssemblyBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedMeasurableKernelAlmostSureOutcomeBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedMeasurableKernelAlmostSureOutcomeBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedMeasurableKernelOutcomeBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedMeasurableKernelOutcomeBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ObservedNonAtomicKernelBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/ObservedNonAtomicKernelBoundary.lean) | P3：通用区间算法与体积定理已进入数学层；本文件仅规划保留原非原子 EFG 及路径柱集等式，本阶段不修改示例 |
| [OccurrenceNonIso.lean](../../EconCSLib/Examples/ExtensiveGame/OccurrenceNonIso.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [PreservationImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/PreservationImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [RandomTermination.lean](../../EconCSLib/Examples/ExtensiveGame/RandomTermination.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [ReachableNoChance.lean](../../EconCSLib/Examples/ExtensiveGame/ReachableNoChance.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [RealizedInformationBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/RealizedInformationBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [RecallHierarchy.lean](../../EconCSLib/Examples/ExtensiveGame/RecallHierarchy.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [RecallImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/RecallImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [RestartImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/RestartImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [ReusableSemantics.lean](../../EconCSLib/Examples/ExtensiveGame/ReusableSemantics.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [RootImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/RootImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [RootScopedKuhn.lean](../../EconCSLib/Examples/ExtensiveGame/RootScopedKuhn.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [StochasticTreeCompilation.lean](../../EconCSLib/Examples/ExtensiveGame/StochasticTreeCompilation.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [StochasticWinningImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/StochasticWinningImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [StructuralCoreImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/StructuralCoreImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [StructuralTermination.lean](../../EconCSLib/Examples/ExtensiveGame/StructuralTermination.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [TerminalKernelBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/TerminalKernelBoundary.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [TerminalStoppedExecution.lean](../../EconCSLib/Examples/ExtensiveGame/TerminalStoppedExecution.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [TwoStepImperfectNoWinner.lean](../../EconCSLib/Examples/ExtensiveGame/TwoStepImperfectNoWinner.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |
| [WinningImportBoundary.lean](../../EconCSLib/Examples/ExtensiveGame/WinningImportBoundary.lean) | 保留导入边界回归；P5 随实际导出变化同步预期 |
| [WinningSemantics.lean](../../EconCSLib/Examples/ExtensiveGame/WinningSemantics.lean) | 保留具体模型、语义边界或反例；受影响时改为主库接口消费者 |

## 4. 聚合、文档与测试

- [EconCSLib.lean](../../EconCSLib.lean)：维持经治理的精简入口；不聚合 Examples 或 OpenProblem。
- [EconCSLib/Examples.lean](../../EconCSLib/Examples.lean)：继续聚合示例和执行回归。
- 文档、审计脚本、基线与测试文件的分工和验收见[整体规划第 7 节](efg-file-plan.md#7-实施顺序与验收文件)。
- 当前没有 EFG 专用 `OpenProblem` 模块；未来数学缺口先登记知识节点或 issue，不预建占位 Lean 文件。
