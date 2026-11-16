import PlattPointSubsetKernel
import PlattPointPackets.S8B000108
import PlattPointPackets.S8B000109
import PlattPointPackets.S8B000110
import PlattPointPackets.S8B000111
import PlattPointPackets.S8B000112
import PlattPointPackets.S8B000113
import PlattPointPackets.S8B000114
import PlattPointPackets.S8B000115
import PlattPointPackets.S8B000116
import PlattPointPackets.S8B000117
import PlattPointPackets.S8B000118
import PlattPointPackets.S8B000119
import PlattPointPackets.S8B000120
import PlattPointPackets.S8B000121
import PlattPointPackets.S8B000122
import PlattPointPackets.S8B000123
import PlattPointPackets.S8B000124
import PlattPointPackets.S8B000125
import PlattPointPackets.S8B000126
import PlattGlobalGrid.S8B000112
namespace ChenEffective.PlattWindow.PointCovers.S8B000112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000108.points ++ ChenEffective.PlattWindow.PointPackets.S8B000109.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000110.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000111.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000126.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000112.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000112.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000112
