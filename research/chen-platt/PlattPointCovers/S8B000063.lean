import PlattPointSubsetKernel
import PlattPointPackets.S5B000298
import PlattPointPackets.S5B000299
import PlattPointPackets.S5B000300
import PlattPointPackets.S5B000301
import PlattPointPackets.S5B000302
import PlattPointPackets.S5B000303
import PlattPointPackets.S5B000304
import PlattPointPackets.S5B000305
import PlattPointPackets.S5B000306
import PlattPointPackets.S5B000307
import PlattPointPackets.S5B000308
import PlattPointPackets.S5B000309
import PlattPointPackets.S5B000310
import PlattGlobalGrid.S8B000063
namespace ChenEffective.PlattWindow.PointCovers.S8B000063
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((ChenEffective.PlattWindow.PointPackets.S5B000298.points ++ ChenEffective.PlattWindow.PointPackets.S5B000299.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000310.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000063.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000063.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000063
