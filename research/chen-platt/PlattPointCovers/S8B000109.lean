import PlattPointSubsetKernel
import PlattPointPackets.S8B000053
import PlattPointPackets.S8B000054
import PlattPointPackets.S8B000055
import PlattPointPackets.S8B000056
import PlattPointPackets.S8B000057
import PlattPointPackets.S8B000058
import PlattPointPackets.S8B000059
import PlattPointPackets.S8B000060
import PlattPointPackets.S8B000061
import PlattPointPackets.S8B000062
import PlattPointPackets.S8B000063
import PlattPointPackets.S8B000064
import PlattPointPackets.S8B000065
import PlattPointPackets.S8B000066
import PlattPointPackets.S8B000067
import PlattPointPackets.S8B000068
import PlattPointPackets.S8B000069
import PlattPointPackets.S8B000070
import PlattPointPackets.S8B000071
import PlattGlobalGrid.S8B000109
namespace ChenEffective.PlattWindow.PointCovers.S8B000109
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000053.points ++ ChenEffective.PlattWindow.PointPackets.S8B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000064.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000065.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000066.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000067.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000068.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000069.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000070.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000071.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000109.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000109.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000109
