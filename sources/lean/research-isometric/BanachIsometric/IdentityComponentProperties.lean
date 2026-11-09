import BanachIsometric.ComponentCovering

/-! The connected structure group in the component reduction is genuinely
connected and compact in its inherited topology. -/

namespace BanachIsometric

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem connectedSpace_connectedComponentOfOne :
    ConnectedSpace (Subgroup.connectedComponentOfOne G) := by
  change ConnectedSpace (connectedComponent (1 : G))
  exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

theorem compactSpace_connectedComponentOfOne [CompactSpace G] :
    CompactSpace (Subgroup.connectedComponentOfOne G) := by
  change CompactSpace (connectedComponent (1 : G))
  exact isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact

end BanachIsometric
