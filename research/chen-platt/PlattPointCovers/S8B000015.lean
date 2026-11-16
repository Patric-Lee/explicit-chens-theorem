import PlattPointSubsetKernel
import PlattPointPackets.S4B000114
import PlattPointPackets.S4B000115
import PlattPointPackets.S4B000116
import PlattPointPackets.S4B000117
import PlattPointPackets.S4B000118
import PlattPointPackets.S4B000119
import PlattPointPackets.S4B000120
import PlattPointPackets.S4B000121
import PlattPointPackets.S4B000122
import PlattGlobalGrid.S8B000015
namespace ChenEffective.PlattWindow.PointCovers.S8B000015
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((ChenEffective.PlattWindow.PointPackets.S4B000114.points ++ ChenEffective.PlattWindow.PointPackets.S4B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000122.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000015.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000015.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000015
