import PlattPointSubsetKernel
import PlattPointPackets.S7B000111
import PlattPointPackets.S7B000112
import PlattPointPackets.S7B000113
import PlattPointPackets.S7B000114
import PlattPointPackets.S7B000115
import PlattPointPackets.S7B000116
import PlattPointPackets.S7B000117
import PlattPointPackets.S7B000118
import PlattPointPackets.S7B000119
import PlattPointPackets.S7B000120
import PlattPointPackets.S7B000121
import PlattPointPackets.S7B000122
import PlattPointPackets.S7B000123
import PlattPointPackets.S7B000124
import PlattPointPackets.S7B000125
import PlattPointPackets.S7B000126
import PlattPointPackets.S7B000127
import PlattGlobalGrid.S8B000094
namespace ChenEffective.PlattWindow.PointCovers.S8B000094
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000111.points ++ ChenEffective.PlattWindow.PointPackets.S7B000112.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000113.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000114.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000115.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000127.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000094.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000094.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000094
