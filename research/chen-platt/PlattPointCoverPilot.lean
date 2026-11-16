import PlattPointPackets.L0B0000
import PlattGlobalGrid.L0B0000

namespace ChenEffective.PlattWindow
set_option maxHeartbeats 0
set_option maxRecDepth 3000000

/-- Representative stream-merge check against the already checked packet and
grid trees, before loading the entire global certificate closure. -/
theorem point_cover_pilot :
    checkPointCoverAux 1000000 PointPackets.L0B0000.points GlobalGrid.L0B0000.points=true := by
  decide +kernel

#print axioms point_cover_pilot
end ChenEffective.PlattWindow
