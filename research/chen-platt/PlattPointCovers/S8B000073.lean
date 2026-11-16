import PlattPointSubsetKernel
import PlattPointPackets.S6B000115
import PlattPointPackets.S6B000116
import PlattPointPackets.S6B000117
import PlattPointPackets.S6B000118
import PlattPointPackets.S6B000119
import PlattPointPackets.S6B000120
import PlattPointPackets.S6B000121
import PlattPointPackets.S6B000122
import PlattPointPackets.S6B000123
import PlattPointPackets.S6B000124
import PlattPointPackets.S6B000125
import PlattPointPackets.S6B000126
import PlattPointPackets.S6B000127
import PlattPointPackets.S6B000128
import PlattPointPackets.S6B000129
import PlattGlobalGrid.S8B000073
namespace ChenEffective.PlattWindow.PointCovers.S8B000073
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000115.points ++ ChenEffective.PlattWindow.PointPackets.S6B000116.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000117.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000118.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000119.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000120.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000121.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000122.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000123.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000124.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000125.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000126.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000127.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000128.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000129.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000073.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000073.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000073
