import PlattPointSubsetKernel
import PlattPointPackets.S4B000105
import PlattPointPackets.S4B000106
import PlattPointPackets.S4B000107
import PlattPointPackets.S4B000108
import PlattPointPackets.S4B000109
import PlattPointPackets.S4B000110
import PlattPointPackets.S4B000111
import PlattPointPackets.S4B000112
import PlattPointPackets.S4B000113
import PlattPointPackets.S4B000114
import PlattGlobalGrid.S8B000014
namespace ChenEffective.PlattWindow.PointCovers.S8B000014
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((ChenEffective.PlattWindow.PointPackets.S4B000105.points ++ ChenEffective.PlattWindow.PointPackets.S4B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000114.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000014.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000014.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000014
