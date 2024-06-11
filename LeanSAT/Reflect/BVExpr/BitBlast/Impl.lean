import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Pred
import LeanSAT.AIG.BoolExprCached

namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : AIG.Entrypoint BVBit :=
  AIG.ofBoolExprCached expr BVPred.bitblast

end BVLogicalExpr
