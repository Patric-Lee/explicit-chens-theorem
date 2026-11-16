import PlattPointSubsetKernel
import PlattPointPackets.S5B000111
import PlattPointPackets.S5B000112
import PlattPointPackets.S5B000113
import PlattPointPackets.S5B000114
import PlattPointPackets.S5B000115
import PlattPointPackets.S5B000116
import PlattPointPackets.S5B000117
import PlattPointPackets.S5B000118
import PlattPointPackets.S5B000119
import PlattPointPackets.S5B000120
import PlattPointPackets.S5B000121
import PlattPointPackets.S5B000122
import PlattGlobalGrid.S8B000047
namespace ChenEffective.PlattWindow.PointCovers.S8B000047
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((((((((ChenEffective.PlattWindow.PointPackets.S5B000111.points ++ ChenEffective.PlattWindow.PointPackets.S5B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S5B000122.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000047.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000047.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000047
