import PlattPointSubsetKernel
import PlattPointPackets.S6B000102
import PlattPointPackets.S6B000103
import PlattPointPackets.S6B000104
import PlattPointPackets.S6B000105
import PlattPointPackets.S6B000106
import PlattPointPackets.S6B000107
import PlattPointPackets.S6B000108
import PlattPointPackets.S6B000109
import PlattPointPackets.S6B000110
import PlattPointPackets.S6B000111
import PlattPointPackets.S6B000112
import PlattPointPackets.S6B000113
import PlattPointPackets.S6B000114
import PlattPointPackets.S6B000115
import PlattGlobalGrid.S8B000072
namespace ChenEffective.PlattWindow.PointCovers.S8B000072
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000102.points ++ ChenEffective.PlattWindow.PointPackets.S6B000103.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000104.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000105.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000106.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000107.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000108.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000115.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000072.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000072.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000072
