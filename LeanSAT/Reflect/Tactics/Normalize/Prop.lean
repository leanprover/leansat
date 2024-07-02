/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import LeanSAT.Reflect.Tactics.Attr

namespace BVDecide
namespace Normalize

attribute [bv_normalize] not_true
attribute [bv_normalize] and_true
attribute [bv_normalize] true_and
attribute [bv_normalize] or_true
attribute [bv_normalize] true_or

end Normalize
end BVDecide
