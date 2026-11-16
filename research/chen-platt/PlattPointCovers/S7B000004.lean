import PlattPointSubsetKernel
import PlattPointPackets.S2B000061
import PlattPointPackets.S2B000062
import PlattPointPackets.S2B000063
import PlattPointPackets.S2B000064
import PlattGlobalGrid.S7B000004
namespace ChenEffective.PlattWindow.PointCovers.S7B000004
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000061.points ++ ChenEffective.PlattWindow.PointPackets.S2B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000064.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000004.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000004.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000004
