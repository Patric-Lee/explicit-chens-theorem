import PlattPointSubsetKernel
import PlattPointPackets.S5B000057
import PlattPointPackets.S5B000058
import PlattPointPackets.S5B000059
import PlattPointPackets.S5B000060
import PlattPointPackets.S5B000061
import PlattPointPackets.S5B000062
import PlattPointPackets.S5B000063
import PlattPointPackets.S5B000064
import PlattPointPackets.S5B000065
import PlattPointPackets.S5B000066
import PlattPointPackets.S5B000067
import PlattPointPackets.S5B000068
import PlattGlobalGrid.S8B000042
namespace ChenEffective.PlattWindow.PointCovers.S8B000042
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000057.points ++ ChenEffective.PlattWindow.PointPackets.S5B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000068.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000042.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000042.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000042
