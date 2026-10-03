import VCVio.OracleComp.QueryTracking.Structures

namespace OracleSpec.QueryCache
instance (priority := high) instLEExtension {ι : Type*} {spec : OracleSpec ι} :
    LE (QueryCache spec) :=
  @Preorder.toLE _ (@PartialOrder.toPreorder _ QueryCache.instPartialOrder)
end OracleSpec.QueryCache
