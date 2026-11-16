import PlattPointSubsetKernel
import PlattPointPackets.S6B000049
import PlattPointPackets.S6B000050
import PlattPointPackets.S6B000051
import PlattPointPackets.S6B000052
import PlattPointPackets.S6B000053
import PlattPointPackets.S6B000054
import PlattPointPackets.S6B000055
import PlattPointPackets.S6B000056
import PlattPointPackets.S6B000057
import PlattPointPackets.S6B000058
import PlattPointPackets.S6B000059
import PlattPointPackets.S6B000060
import PlattPointPackets.S6B000061
import PlattPointPackets.S6B000062
import PlattGlobalGrid.S8B000068
namespace ChenEffective.PlattWindow.PointCovers.S8B000068
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000049.points ++ ChenEffective.PlattWindow.PointPackets.S6B000050.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000051.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000052.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000053.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000054.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000055.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000056.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000057.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000058.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000059.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000060.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000061.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000062.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000068.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000068.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000068
