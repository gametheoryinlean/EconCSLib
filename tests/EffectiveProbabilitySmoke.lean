import EconCSLib.Math.Probability.Effective

/-!
# Effective probability smoke tests

These checks execute only the measure-free layer.  They cover an exact
non-atomic event query, a simple-observable expectation, and bind through a
constant effective kernel.
-/

namespace EffectiveProbabilitySmoke

open EffectiveProbability
open EffectiveProbability.UniformUnitInterval

private def halfInterval : EventCode :=
  [((1 / 4 : ℚ), (3 / 4 : ℚ))]

private theorem tolerance_pos : (0 : ℚ) < 1 / 100 := by
  norm_num

example :
    ((law.mass halfInterval).query (1 / 100) tolerance_pos).lower = 1 / 2 := by
  native_decide

example :
    ((law.mass halfInterval).query (1 / 100) tolerance_pos).upper = 1 / 2 := by
  native_decide

private def observable : SimpleObservable EventCode :=
  .add (.const 1) (.scale 2 (.indicator halfInterval))

example : expectRat observable = 2 := by
  native_decide

example :
    ((law.expect observable).query (1 / 100) tolerance_pos).lower = 2 := by
  native_decide

private def sourceLaw : EffectiveLaw Unit where
  mass _ := RatOracle.exact 1

example :
    (((sourceLaw.bind (kernel Unit)).mass halfInterval).query
        (1 / 100) tolerance_pos).upper = 1 / 2 := by
  native_decide

end EffectiveProbabilitySmoke
