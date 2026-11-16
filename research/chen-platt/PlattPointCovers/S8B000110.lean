import PlattPointSubsetKernel
import PlattPointPackets.S8B000071
import PlattPointPackets.S8B000072
import PlattPointPackets.S8B000073
import PlattPointPackets.S8B000074
import PlattPointPackets.S8B000075
import PlattPointPackets.S8B000076
import PlattPointPackets.S8B000077
import PlattPointPackets.S8B000078
import PlattPointPackets.S8B000079
import PlattPointPackets.S8B000080
import PlattPointPackets.S8B000081
import PlattPointPackets.S8B000082
import PlattPointPackets.S8B000083
import PlattPointPackets.S8B000084
import PlattPointPackets.S8B000085
import PlattPointPackets.S8B000086
import PlattPointPackets.S8B000087
import PlattPointPackets.S8B000088
import PlattPointPackets.S8B000089
import PlattGlobalGrid.S8B000110
namespace ChenEffective.PlattWindow.PointCovers.S8B000110
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S8B000071.points ++ ChenEffective.PlattWindow.PointPackets.S8B000072.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000073.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000074.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000075.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000076.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000077.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000078.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000079.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000080.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000081.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000082.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000083.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000084.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000085.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000086.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000089.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000110.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000110.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000110
