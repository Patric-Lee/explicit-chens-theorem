import PlattPointSubsetKernel
import PlattPointPackets.S7B000048
import PlattPointPackets.S7B000049
import PlattPointPackets.S7B000050
import PlattPointPackets.S7B000051
import PlattPointPackets.S7B000052
import PlattPointPackets.S7B000053
import PlattPointPackets.S7B000054
import PlattPointPackets.S7B000055
import PlattPointPackets.S7B000056
import PlattPointPackets.S7B000057
import PlattPointPackets.S7B000058
import PlattPointPackets.S7B000059
import PlattPointPackets.S7B000060
import PlattPointPackets.S7B000061
import PlattPointPackets.S7B000062
import PlattPointPackets.S7B000063
import PlattPointPackets.S7B000064
import PlattGlobalGrid.S8B000090
namespace ChenEffective.PlattWindow.PointCovers.S8B000090
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000048.points ++ ChenEffective.PlattWindow.PointPackets.S7B000049.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000062.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000063.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000064.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000090.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000090.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000090
