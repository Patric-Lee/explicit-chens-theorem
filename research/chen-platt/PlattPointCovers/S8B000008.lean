import PlattPointSubsetKernel
import PlattPointPackets.S4B000056
import PlattPointPackets.S4B000057
import PlattPointPackets.S4B000058
import PlattPointPackets.S4B000059
import PlattPointPackets.S4B000060
import PlattPointPackets.S4B000061
import PlattPointPackets.S4B000062
import PlattPointPackets.S4B000063
import PlattPointPackets.S4B000064
import PlattGlobalGrid.S8B000008
namespace ChenEffective.PlattWindow.PointCovers.S8B000008
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000056.points ++ ChenEffective.PlattWindow.PointPackets.S4B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000064.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000008.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000008.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000008
