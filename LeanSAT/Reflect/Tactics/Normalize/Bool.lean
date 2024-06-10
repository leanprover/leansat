import LeanSAT.Reflect.Tactics.Attr

namespace BVDecide
namespace Normalize

attribute [bv_normalize] Bool.not_true
attribute [bv_normalize] Bool.not_false
attribute [bv_normalize] Bool.or_true
attribute [bv_normalize] Bool.true_or
attribute [bv_normalize] Bool.or_false
attribute [bv_normalize] Bool.false_or
attribute [bv_normalize] Bool.and_true
attribute [bv_normalize] Bool.true_and
attribute [bv_normalize] Bool.and_false
attribute [bv_normalize] Bool.false_and
attribute [bv_normalize] beq_self_eq_true'
attribute [bv_normalize] Bool.not_beq_false
attribute [bv_normalize] Bool.not_beq_true
attribute [bv_normalize] Bool.beq_true
attribute [bv_normalize] Bool.true_beq
attribute [bv_normalize] Bool.beq_false
attribute [bv_normalize] Bool.false_beq
attribute [bv_normalize] Bool.beq_not_self
attribute [bv_normalize] Bool.not_beq_self
attribute [bv_normalize] Bool.beq_self_left
attribute [bv_normalize] Bool.beq_self_right
attribute [bv_normalize] Bool.not_not

end Normalize
end BVDecide
