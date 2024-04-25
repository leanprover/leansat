import LeanSAT.Reflect.BVExpr.BitBlast.Impl.Pred

namespace BVLogicalExpr

def bitblast (expr : BVLogicalExpr) : AIG.Entrypoint BVBit :=
  AIG.ofBoolExprCached expr BVPred.bitblast

end BVLogicalExpr
